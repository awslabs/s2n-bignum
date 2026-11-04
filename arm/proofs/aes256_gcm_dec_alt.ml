(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* AES-256-GCM decryption of whole blocks, 8 blocks at a time: the 8-way     *)
(* kernel aes256_gcm_dec_alt.                                                *)
(*                                                                           *)
(* Contract (AES256_GCM_DEC_ALT_SUBROUTINE_CORRECT).  The kernel processes   *)
(* nblk = gcm_wb_blocks bit_len whole 16-byte blocks (none when bit_len is   *)
(* not a multiple of 128) and returns 16 * nblk.  Given the FIPS-197 key     *)
(* schedule rk at key_p, the key table htable_mem_8 at htbl_p for the GHASH  *)
(* key                                                                       *)
(*   H = aes256_cipher (word 0) rk                                           *)
(* and the counter block ctr_block nonce c at ivec_p, output block j is      *)
(* input block j XOR aes_ctr_block aes256_cipher c nonce rk j, the tag at    *)
(* xi_p becomes nist_ghash H over the input (ciphertext) blocks, continued   *)
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
(* invalid bit_len, and the prologue (0xc..0x18) saves d8-d15.  The core     *)
(* runs from pc + 0x1c to its exit pc + 4556 (0x11cc,                        *)
(* L256_dec_frame_restore); its theorem AES256_GCM_DEC_ALT_CORRECT comes     *)
(* from the spine WBN_DEC_CORE_BYTELIST, which splits on nblk:               *)
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
(* The file holds, in order: the key-table known-answer instances; the       *)
(* binary-independent layer (GHASH/Karatsuba bridge, SIMD-fold steppers,     *)
(* counter core, CTR and decrypt specifications); the machine code; the      *)
(* <=8-block chain (band tails, shared front, small-input path, readable     *)
(* band and dispatch theorems); the nblk > 8 proof in sections 1 to 12       *)
(* (section 2, the symbolic counter layer, comes earlier, with the band      *)
(* tails that use it); the spines and the exported theorems; the             *)
(* constant-time and memory-safety proof.                                    *)
(* ========================================================================= *)


(* The specification vocabulary and lemmas shared with the other AES-GCM
   proofs (ctr_block, nist_input_block, htable_mem_8, HTABLE_MEM_8_FLAT,
   gcm_wb_blocks, DISCARD_STALE_TAC, ...). *)
needs "arm/proofs/utils/aes_gcm_common.ml";;

(* ========================================================================= *)
(* Known-answer instances of htable_mem_8 at two concrete AES-256 keys.      *)
(*                                                                           *)
(* In the shared AES-GCM vocabulary the GHASH key is                         *)
(* H = aes256_cipher (word 0) rk, with rk the FIPS-197 key schedule, and the *)
(* key table precondition of the 8-way kernels is                            *)
(* htable_mem_8 (ghash_twist H) htbl_p s.  Below that precondition is        *)
(* evaluated, for the all-zero key and for the McGrew-Viega GCM test case 15 *)
(* key (the key schedules of common/fips197.ml), to the 12 table entries.    *)
(* They are the bytes gcm_init_v8 writes for those keys, and the bytes       *)
(* ref_gcm_init_htable writes in the C test "aes_gcm_htable" (tests/test.c), *)
(* so they tie the precondition to the real table: stated with a wrong H,    *)
(* such as the byte-reversed one at the end, it does not match them.         *)
(* ========================================================================= *)


(* All-zero key: H = dc95c078a2408989ad48a21492842087. *)

let HTABLE_MEM_8_AESAVS_ZERO_KEY_256 = prove
 (`!ptr s.
     htable_mem_8
       (ghash_twist (aes256_cipher (word 0) AESAVS_ZERO_KEY_256_SCHEDULE))
       ptr s <=>
     read (memory :> bytes128 ptr) s =
       word 0x5a9144292508410f7b2b80f144811313 /\
     read (memory :> bytes128 (word_add ptr (word 16))) s =
       word 0x18815f770318b11721bac4d86189521c /\
     read (memory :> bytes128 (word_add ptr (word 32))) s =
       word 0x5505a2719d24c36f4d84fd069e3c7278 /\
     read (memory :> bytes128 (word_add ptr (word 48))) s =
       word 0x8cc3bf92b3c5611f175e7336e8418ee0 /\
     read (memory :> bytes128 (word_add ptr (word 64))) s =
       word 0xba81c249997cd6fd9b9dcca45b84efff /\
     read (memory :> bytes128 (word_add ptr (word 80))) s =
       word 0xf27b604459a2c40248faa20dc0de12ff /\
     read (memory :> bytes128 (word_add ptr (word 96))) s =
       word 0xf39c9203a58c04ab9eb1c1ebb05c4519 /\
     read (memory :> bytes128 (word_add ptr (word 112))) s =
       word 0x1ea16b4e105889f96d2d53e815d041b2 /\
     read (memory :> bytes128 (word_add ptr (word 128))) s =
       word 0x2a0cb6bcb97d97a834adddf2a9251e51 /\
     read (memory :> bytes128 (word_add ptr (word 144))) s =
       word 0xa14610bf3e3af4c23287a42fbc7357c2 /\
     read (memory :> bytes128 (word_add ptr (word 160))) s =
       word 0x19ae23037094693f93c1b4908249a300 /\
     read (memory :> bytes128 (word_add ptr (word 176))) s =
       word 0x6d9364db65b87552743d47d8152c1c6d`,
  REPEAT GEN_TAC THEN
  CONV_TAC(LAND_CONV(HTABLE_MEM_8_KEY_CONV aes256_cipher
                       AESAVS_ZERO_KEY_256_SCHEDULE)) THEN
  REFL_TAC);;

(* GCM test case 15 key: H = acbef20579b4b8ebce889bac8732dad7. *)

let HTABLE_MEM_8_NIST_TC15_KEY = prove
 (`!ptr s.
     htable_mem_8
       (ghash_twist (aes256_cipher (word 0) NIST_TC15_KEY_SCHEDULE))
       ptr s <=>
     read (memory :> bytes128 ptr) s =
       word 0x9d1137590e65b5af9b7de40af36971d7 /\
     read (memory :> bytes128 (word_add ptr (word 16))) s =
       word 0x6250d1e611963320066cd353fd0cc478 /\
     read (memory :> bytes128 (word_add ptr (word 32))) s =
       word 0x176ea7748156c4f7753e769290c0f7d7 /\
     read (memory :> bytes128 (word_add ptr (word 48))) s =
       word 0x4dacf0715be378138f106846b8c7ae56 /\
     read (memory :> bytes128 (word_add ptr (word 64))) s =
       word 0xa11c7beedb2faa97c2bc9837e324d645 /\
     read (memory :> bytes128 (word_add ptr (word 80))) s =
       word 0x11818ff911a91b65b09df417ca86b1f2 /\
     read (memory :> bytes128 (word_add ptr (word 96))) s =
       word 0x90b5acfc5229d0fae997267d30d323f3 /\
     read (memory :> bytes128 (word_add ptr (word 112))) s =
       word 0x5ad8655f4ae49a2f79228a8162faf309 /\
     read (memory :> bytes128 (word_add ptr (word 128))) s =
       word 0x9ad471bb94ce90d0c00c14e4de2a0aff /\
     read (memory :> bytes128 (word_add ptr (word 144))) s =
       word 0xd230a7e922dc7379c75ff4dd09d4a3be /\
     read (memory :> bytes128 (word_add ptr (word 160))) s =
       word 0xfd00063de14f053f156f53342b08d0c7 /\
     read (memory :> bytes128 (word_add ptr (word 176))) s =
       word 0x1387f5ed06b50431ee87f3d0e7fa010e`,
  REPEAT GEN_TAC THEN
  CONV_TAC(LAND_CONV(HTABLE_MEM_8_KEY_CONV aes256_cipher
                       NIST_TC15_KEY_SCHEDULE)) THEN
  REFL_TAC);;

(* The byte-reversed key word_reversefields 8 H (the little-endian reading   *)
(* of AES_K(0^128)) describes a different table: at the all-zero key none of *)
(* its 12 entries equals the real one, so a key-table precondition stated    *)
(* with it is not satisfied by the table gcm_init_v8 builds.                 *)

let HTABLE_MEM_8_AESAVS_ZERO_KEY_256_REVERSED_H = prove
 (`!ptr s.
     htable_mem_8
       (ghash_twist (aes256_cipher (word 0) AESAVS_ZERO_KEY_256_SCHEDULE))
       ptr s
     ==> ~htable_mem_8
            (ghash_twist (word_reversefields 8
               (aes256_cipher (word 0) AESAVS_ZERO_KEY_256_SCHEDULE)))
            ptr s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HTABLE_MEM_8_AESAVS_ZERO_KEY_256] THEN
  CONV_TAC(RAND_CONV(RAND_CONV(HTABLE_MEM_8_KEY_CONV aes256_cipher
                                 AESAVS_ZERO_KEY_256_SCHEDULE))) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV);;

(* ========================================================================= *)
(* Binary-independent proof machinery.                                       *)
(*                                                                           *)
(* Everything from here to the machine code is independent of the kernel:    *)
(* - the N-block GHASH Karatsuba layer and the GMULTn builder;               *)
(* - the counter core (gcm_ctr_inc, inc32, gcm_ctr_inc_iter);                *)
(* - the AES-256 counter-mode output specification (aes_ctr) and the         *)
(*   byte-list lemmas;                                                       *)
(* - the generic GCM machinery: the GHASH/Karatsuba bridge lemmas, such as   *)
(*   KARATSUBA_LIMBS_LET, GHASH_1BLOCK_CORRECT and GMULT_FULL_CORRECT_BA;    *)
(* - the SIMD-fold stepping layer, such as GCM_SIMD_SIMPLIFY_TAC, the        *)
(*   per-step-discard steppers and ARM_VSTEPS_FOLD_TAC;                      *)
(* - the bridge-close helpers, such as PMUL_CONG_128,                        *)
(*   ABBREV_INNER_PMULS_TAC, QQ0SPLIT and JOINMID;                           *)
(* - the N-block bridge infrastructure (JOIN_EQ_SPLIT, the SUBW_* lane       *)
(*   lemmas, MERGE_2BLK_TAC, GMULT2_FULL_CORRECT_BA, LANE_CLOSE_TAC);        *)
(* - the decrypt specification (gcm_dec_ghash_blocks, gcm_dec_final_xi,      *)
(*   gcm_dec_pt_bytes).                                                      *)
(*                                                                           *)
(* No machine code is defined here.                                          *)
(* ========================================================================= *)

needs "arm/proofs/utils/aes.ml";;
needs "arm/proofs/utils/aes_encrypt_spec.ml";;

(* ========================================================================= *)
(* N-block GHASH Karatsuba layer.                                            *)
(*                                                                           *)
(* Contents: HELPER_3 and GHASH_POLYVAL_ACC_3/4/5 (3/4/5-block Horner        *)
(* unrolling), the KARATSUBA_LIMBS lemmas, and the layer of                  *)
(* karatsuba_block_p{l,h,m}, kara_acc, pack_corrected, kara_quad_* and       *)
(* project_triples, whose KARA_ACC_PACK_HELPER equates the packed            *)
(* XOR-accumulated per-block Karatsuba triples with the XOR of the per-block *)
(* word_pmul products.                                                       *)
(*                                                                           *)
(* It builds on common/polyval_ghash.ml and common/karatsuba_pmul.ml.        *)
(* ========================================================================= *)


(* ---- GHASH spec extras (3/4/5-block Horner unrolling) ---- *)

(* Helper:                                                                   *)
(*   polyval_dot(a XOR p, h)*h^2 == a*h^3 + p*h^3 (mod Q), where             *)
(*   h^2 = polyval_dot h h and h^3 = polyval_dot h (polyval_dot h h).        *)
(* It bridges via INNER_CONG_GEN, after commuting the two factors of         *)
(* polyval_dot h h^2 (by WORD_PMUL_SYM).                                     *)

let HELPER_3 = prove
 (`!(a:int128) (p:int128) (h:int128).
    (ring_mul bool_poly (poly_of_word (polyval_dot (word_xor a p) h))
       (poly_of_word (polyval_dot h h)) ==
     ring_add bool_poly
       (ring_mul bool_poly (poly_of_word a) (poly_of_word (polyval_dot h (polyval_dot h h))))
       (ring_mul bool_poly (poly_of_word p) (poly_of_word (polyval_dot h (polyval_dot h h)))))
    mod_polyval`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
  EXISTS_TAC
    `ring_mul bool_poly
      (ring_add bool_poly (poly_of_word (a:int128)) (poly_of_word (p:int128)))
      (poly_of_word (polyval_dot (h:int128) (polyval_dot h h)))` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `polyval_dot (h:int128) (polyval_dot h h) = polyval_dot (polyval_dot (h:int128) h) h`
      SUBST1_TAC THENL
     [REWRITE_TAC[polyval_dot] THEN REWRITE_TAC[WORD_PMUL_SYM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`h:int128`; `word_xor (a:int128) (p:int128)`; `1`] INNER_CONG_GEN) THEN
    REWRITE_TAC[TWO; ONE; h_power; POLY_OF_WORD_XOR];
    MATCH_MP_TAC MOD_POLYVAL_REFL_GEN THEN
    SIMP_TAC[RING_MUL; RING_ADD; BOOL_POLY_OF_WORD] THEN
    MATCH_MP_TAC(GSYM RING_ADD_RDISTRIB) THEN REWRITE_TAC[BOOL_POLY_OF_WORD]]);;

let GHASH_POLYVAL_ACC_3 = prove
 (`!(h:int128) (a:int128) (p:int128) (q:int128) (r:int128).
    ghash_polyval_acc h a [p:int128; q; r] =
    polyval_reduce_prop3
      (word_xor
        (word_pmul (word_xor a p) (polyval_dot h (polyval_dot h h)) : 256 word)
       (word_xor
        (word_pmul q (polyval_dot h h) : 256 word)
        (word_pmul r h : 256 word)))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [ghash_polyval_acc] THEN
  REWRITE_TAC[GHASH_POLYVAL_ACC_2] THEN
  REWRITE_TAC[WORD_PMUL_XOR] THEN
  MATCH_MP_TAC(ISPEC `128` MOD_POLYVAL_CANCEL_VARPOW) THEN
  MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
  EXISTS_TAC
    `poly_of_word (word_xor
      (word_xor (word_pmul (polyval_dot (word_xor (a:int128) (p:int128)) (h:int128)) (polyval_dot h h))
                (word_pmul (q:int128) (polyval_dot h h)))
      (word_pmul (r:int128) (h:int128)) : 256 word)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[POLYVAL_REDUCE_PROP3_CORRECT];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[MOD_POLYVAL_SYM] THEN
  MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
  EXISTS_TAC
    `poly_of_word (word_xor
      (word_xor (word_pmul (a:int128) (polyval_dot h (polyval_dot h h)))
                (word_pmul (p:int128) (polyval_dot h (polyval_dot h h))))
      (word_xor (word_pmul (q:int128) (polyval_dot h h))
                (word_pmul (r:int128) (h:int128))) : 256 word)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[POLYVAL_REDUCE_PROP3_CORRECT];
    ALL_TAC] THEN
  REWRITE_TAC[POLY_OF_WORD_XOR; POLY_OF_WORD_PMUL_2N] THEN
  MP_TAC(SPECL [`a:int128`; `p:int128`; `h:int128`] HELPER_3) THEN
  REWRITE_TAC[mod_polyval] THEN DISCH_TAC THEN
  ABBREV_TAC `pX = ring_mul bool_poly (poly_of_word (polyval_dot (word_xor (a:int128) (p:int128)) (h:int128))) (poly_of_word (polyval_dot (h:int128) h))` THEN
  ABBREV_TAC `pY = ring_add bool_poly
    (ring_mul bool_poly (poly_of_word (a:int128)) (poly_of_word (polyval_dot (h:int128) (polyval_dot h h))))
    (ring_mul bool_poly (poly_of_word (p:int128)) (poly_of_word (polyval_dot (h:int128) (polyval_dot h h))))` THEN
  ABBREV_TAC `pQ = ring_mul bool_poly (poly_of_word (q:int128)) (poly_of_word (polyval_dot (h:int128) h))` THEN
  ABBREV_TAC `pR = ring_mul bool_poly (poly_of_word (r:int128)) (poly_of_word (h:int128))` THEN
  SUBGOAL_THEN
    `pX IN ring_carrier bool_poly /\ pY IN ring_carrier bool_poly /\ pQ IN ring_carrier bool_poly /\ pR IN ring_carrier bool_poly`
    STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["pX"; "pY"; "pQ"; "pR"] THEN
    SIMP_TAC[RING_MUL; RING_ADD; BOOL_POLY_OF_WORD];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `ring_add bool_poly (ring_add bool_poly pX pQ) pR =
     ring_add bool_poly pX (ring_add bool_poly pQ pR)`
    SUBST1_TAC THENL
   [MATCH_MP_TAC(GSYM RING_ADD_ASSOC) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOD_POLYVAL_ADD THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[MOD_POLYVAL_SYM] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOD_POLYVAL_REFL_GEN THEN ASM_SIMP_TAC[RING_ADD]]);;

(* ========================================================================= *)
(* GHASH_POLYVAL_ACC_4: the 4-block Horner unrolling, derived directly from  *)
(* GHASH_POLYVAL_ACC_BATCHED for the list [p;q;r;s]; it unfolds h_power 0..3 *)
(* to the polyval_dot chain (h, h^2, h^3, h^4).                              *)
(* ========================================================================= *)

let GHASH_POLYVAL_ACC_4 = prove
 (`!(h:int128) (a:int128) (p:int128) (q:int128) (r:int128) (s:int128).
    ghash_polyval_acc h a [p:int128; q; r; s] =
    polyval_reduce_prop3
      (word_xor
        (word_pmul (word_xor a p) (polyval_dot (polyval_dot (polyval_dot h h) h) h) : 256 word)
       (word_xor
        (word_pmul q (polyval_dot (polyval_dot h h) h) : 256 word)
       (word_xor
        (word_pmul r (polyval_dot h h) : 256 word)
        (word_pmul s h : 256 word))))`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`h:int128`; `[q:int128; r; s]`; `a:int128`; `p:int128`]
                GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide; h_power; ARITH; SUB_0] THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[num_CONV `3`; num_CONV `2`; num_CONV `1`; h_power]);;

(* ========================================================================= *)
(* GHASH_POLYVAL_ACC_5: the 5-block Horner unrolling, derived directly from  *)
(* GHASH_POLYVAL_ACC_BATCHED for the list [p;q;r;s;t]; it unfolds h_power    *)
(* 0..4 to the polyval_dot chain (h, h^2, h^3, h^4, h^5).                    *)
(* ========================================================================= *)

let GHASH_POLYVAL_ACC_5 = prove
 (`!(h:int128) (a:int128) (p:int128) (q:int128) (r:int128) (s:int128) (t:int128).
    ghash_polyval_acc h a [p:int128; q; r; s; t] =
    polyval_reduce_prop3
      (word_xor
        (word_pmul (word_xor a p) (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) : 256 word)
       (word_xor
        (word_pmul q (polyval_dot (polyval_dot (polyval_dot h h) h) h) : 256 word)
       (word_xor
        (word_pmul r (polyval_dot (polyval_dot h h) h) : 256 word)
       (word_xor
        (word_pmul s (polyval_dot h h) : 256 word)
        (word_pmul t h : 256 word)))))`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`h:int128`; `[q:int128; r; s; t]`; `a:int128`; `p:int128`]
                GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide; h_power; ARITH; SUB_0] THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`; h_power]);;

(* ---- the N-block Karatsuba layer ---- *)
let WORD_XOR_0_LEFT = WORD_BITWISE_RULE `word_xor (word 0) x = (x:(N)word)`;;

let KARATSUBA_LIMB_0_63 = prove(
  `!(xl:128 word) (xh:128 word) (mid:128 word).
    word_subword (word_xor (word_xor (word_zx xl : 256 word)
                 (word_shl (word_zx mid : 256 word) 64))
                 (word_shl (word_zx xh : 256 word) 128)) (0,64) : 64 word =
    word_subword xl (0,64)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let KARATSUBA_LIMB_64_127 = prove(
  `!(xl:128 word) (xh:128 word) (mid:128 word).
    word_subword (word_xor (word_xor (word_zx xl : 256 word)
                 (word_shl (word_zx mid : 256 word) 64))
                 (word_shl (word_zx xh : 256 word) 128)) (64,64) : 64 word =
    word_xor (word_subword xl (64,64)) (word_subword mid (0,64))`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let KARATSUBA_LIMB_128_191 = prove(
  `!(xl:128 word) (xh:128 word) (mid:128 word).
    word_subword (word_xor (word_xor (word_zx xl : 256 word)
                 (word_shl (word_zx mid : 256 word) 64))
                 (word_shl (word_zx xh : 256 word) 128)) (128,64) : 64 word =
    word_xor (word_subword xh (0,64)) (word_subword mid (64,64))`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let KARATSUBA_LIMB_192_255 = prove(
  `!(xl:128 word) (xh:128 word) (mid:128 word).
    word_subword (word_xor (word_xor (word_zx xl : 256 word)
                 (word_shl (word_zx mid : 256 word) 64))
                 (word_shl (word_zx xh : 256 word) 128)) (192,64) : 64 word =
    word_subword xh (64,64)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let KARATSUBA_LIMBS = CONJ (CONJ KARATSUBA_LIMB_0_63 KARATSUBA_LIMB_64_127)
                           (CONJ KARATSUBA_LIMB_128_191 KARATSUBA_LIMB_192_255);;

let BYTESWAP128_SUBWORD_LO = prove(
  `!(h:int128). word_subword (byteswap128 h) (0,64):(64)word = word_subword h (64,64)`,
  REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

let BYTESWAP128_SUBWORD_HI = prove(
  `!(h:int128). word_subword (byteswap128 h) (64,64):(64)word = word_subword h (0,64)`,
  REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

(* Karatsuba (pl_k, ph_k, pm_k) for a single block. *)
let karatsuba_block_pl = new_definition
 `karatsuba_block_pl (input:int128) (h_tw:int128) : int128 =
  word_pmul (word_subword input (0,64) :64 word)
            (word_subword h_tw (64,64) :64 word)`;;

let karatsuba_block_ph = new_definition
 `karatsuba_block_ph (input:int128) (h_tw:int128) : int128 =
  word_pmul (word_subword input (64,64) :64 word)
            (word_subword h_tw (0,64) :64 word)`;;

let karatsuba_block_pm = new_definition
 `karatsuba_block_pm (input:int128) (hk:int128) : int128 =
  word_pmul
    (word_xor (word_subword input (0,64) :64 word)
              (word_subword input (64,64) :64 word))
    (word_subword hk (0,64) :64 word)`;;

(* The recursive XOR-sum of (pl, ph, pm) across all blocks. *)
let kara_acc = define
 `(kara_acc ([]:(int128#int128#int128)list) (pl_acc:int128) (ph_acc:int128)
            (pm_acc:int128) = (pl_acc, ph_acc, pm_acc)) /\
  (kara_acc (CONS (input,h_tw,hk) rest) pl_acc ph_acc pm_acc =
    kara_acc rest
      (word_xor pl_acc (karatsuba_block_pl input h_tw))
      (word_xor ph_acc (karatsuba_block_ph input h_tw))
      (word_xor pm_acc (karatsuba_block_pm input hk)))`;;

(* ========================================================================= *)
(* Packing the accumulated Karatsuba triples.                                *)
(*                                                                           *)
(* KARA_ACC_PACK_HELPER is proved by induction on the block list from two    *)
(* structural lemmas:                                                        *)
(*                                                                           *)
(*   KARATSUBA_BLOCK_PACKS_TO_PMUL_CLEAN:                                    *)
(*      pack_corrected (pl_k, ph_k, pm_k) = pmul input_k h_k (256-bit)       *)
(*      under the precondition that hk's low half = karatsuba_mid h_k.       *)
(*                                                                           *)
(*   PACK_CORRECTED_XOR (additivity / linearity):                            *)
(*      pack_corrected commutes with XOR in all three arguments.             *)
(*                                                                           *)
(* kara_acc XOR-folds the per-block (pl, ph, pm), pack_corrected distributes *)
(* over XOR, and each block contributes pmul input_k h_k, so the packed      *)
(* accumulator is the XOR of the per-block products (kara_quad_pmul).        *)
(* ========================================================================= *)

(* Pack-corrected: combines (pl, ph, pm) into the 256-bit Karatsuba layout
   (with mid corrected by XOR pl XOR ph). *)
let pack_corrected = new_definition
 `pack_corrected (pl:int128) (ph:int128) (pm:int128) :256 word =
   word_xor (word_xor
     (word_zx pl :256 word)
     (word_shl (word_zx (word_xor (word_xor pl ph) pm) :256 word) 64))
    (word_shl (word_zx ph :256 word) 128)`;;

(* Per-block pack identity. *)
let KARATSUBA_BLOCK_PACKS_TO_PMUL = prove
 (`!(input:int128) (h:int128) (hk:int128).
    word_subword hk (0,64):(64)word = karatsuba_mid h
    ==>
    (word_xor (word_xor
        (word_zx (karatsuba_block_pl input (byteswap128 h)) :256 word)
        (word_shl (word_zx (word_xor (word_xor
            (karatsuba_block_pl input (byteswap128 h))
            (karatsuba_block_ph input (byteswap128 h)))
          (karatsuba_block_pm input hk)) :256 word) 64))
       (word_shl (word_zx (karatsuba_block_ph input (byteswap128 h)) :256 word) 128)) =
    word_pmul input h : 256 word`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[karatsuba_block_pl; karatsuba_block_ph; karatsuba_block_pm;
              BYTESWAP128_SUBWORD_LO; BYTESWAP128_SUBWORD_HI] THEN
  ASM_REWRITE_TAC[karatsuba_mid] THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF; LET_END_DEF] PMUL_KARATSUBA] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  ABBREV_TAC `(p1:(128)word) = word_pmul (word_subword (input:(128)word) (0,64):(64)word)
                                          (word_subword (h:(128)word) (0,64):(64)word)` THEN
  ABBREV_TAC `(p2:(128)word) = word_pmul (word_subword (input:(128)word) (64,64):(64)word)
                                          (word_subword (h:(128)word) (64,64):(64)word)` THEN
  ABBREV_TAC `(p3:(128)word) = word_pmul
                                  (word_xor (word_subword (input:(128)word) (0,64):(64)word)
                                            (word_subword (input:(128)word) (64,64):(64)word))
                                  (word_xor (word_subword (h:(128)word) (0,64):(64)word)
                                            (word_subword (h:(128)word) (64,64):(64)word))` THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC WORD_RULE);;

let KARATSUBA_BLOCK_PACKS_TO_PMUL_CLEAN = prove
 (`!(input:int128) (h:int128) (hk:int128).
    word_subword hk (0,64):(64)word = karatsuba_mid h
    ==>
    pack_corrected
      (karatsuba_block_pl input (byteswap128 h))
      (karatsuba_block_ph input (byteswap128 h))
      (karatsuba_block_pm input hk) =
    word_pmul input h : 256 word`,
  REWRITE_TAC[pack_corrected; KARATSUBA_BLOCK_PACKS_TO_PMUL]);;

(* pack_corrected is XOR-additive in each argument. *)
let PACK_CORRECTED_XOR = prove
 (`!pl1 ph1 pm1 pl2 ph2 pm2:int128.
   pack_corrected (word_xor pl1 pl2) (word_xor ph1 ph2) (word_xor pm1 pm2) =
   word_xor (pack_corrected pl1 ph1 pm1) (pack_corrected pl2 ph2 pm2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[pack_corrected; WORD_ZX_XOR; WORD_SHL_XOR] THEN
  CONV_TAC WORD_RULE);;

(* One kara_acc step (KARA_ACC_CONS_DESTR) and the linearity of kara_acc
   (KARA_ACC_FIRST): starting at (pl0, ph0, pm0) is the same as starting at
   (0,0,0) and XOR-ing the start into the result. *)
let KARA_ACC_CONS_DESTR = prove
 (`!input h_tw hk rest pl0 ph0 pm0.
    kara_acc (CONS (input,h_tw,hk) rest) pl0 ph0 pm0 =
    kara_acc rest
      (word_xor pl0 (karatsuba_block_pl input h_tw))
      (word_xor ph0 (karatsuba_block_ph input h_tw))
      (word_xor pm0 (karatsuba_block_pm input hk))`,
  REWRITE_TAC[kara_acc]);;

let KARA_ACC_FIRST = prove
 (`!triples (pl0:int128) (ph0:int128) (pm0:int128).
    kara_acc triples pl0 ph0 pm0 =
    (let (pl', ph', pm') = kara_acc triples (word 0) (word 0) (word 0) in
     (word_xor pl0 pl', word_xor ph0 ph', word_xor pm0 pm'))`,
  MATCH_MP_TAC list_INDUCT THEN
  CONJ_TAC THENL
   [REWRITE_TAC[kara_acc; LET_DEF; LET_END_DEF; WORD_XOR_0];
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`input:int128`; `h_tw:int128`; `hk:int128`;
                        `rest:(int128#int128#int128)list`] THEN
    DISCH_TAC THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC[KARA_ACC_CONS_DESTR] THEN
    FIRST_X_ASSUM(fun ih ->
      ONCE_REWRITE_TAC[ih] THEN
      MP_TAC(SPECL [`word_xor (word 0:int128)
                              (karatsuba_block_pl input h_tw)`;
                    `word_xor (word 0:int128)
                              (karatsuba_block_ph input h_tw)`;
                    `word_xor (word 0:int128)
                              (karatsuba_block_pm input hk)`] ih)) THEN
    REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    DISCH_THEN(fun th ->
      ABBREV_TAC `acc_zero = kara_acc rest (word 0:int128) (word 0:int128) (word 0:int128)` THEN
      MP_TAC th) THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    SPEC_TAC(`acc_zero:int128#int128#int128`,`q:int128#int128#int128`) THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[PAIR_EQ] THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_RULE]);;

(* Lists of quads (input, h_tw, hk, h), one per block: kara_quad_pmul XORs the
   products word_pmul input h into acc; kara_quad_ok is the bridge precondition
   that every triple comes from a real key h (h_tw = byteswap128 h, and the low
   half of hk is karatsuba_mid h); project_triples drops the h. *)
let kara_quad_pmul = define
  `(kara_quad_pmul ([]:(int128#int128#int128#int128)list) (acc:256 word) = acc) /\
   (kara_quad_pmul (CONS (input,h_tw,hk,h) qrest) acc =
     kara_quad_pmul qrest (word_xor acc (word_pmul input h:256 word)))`;;

let kara_quad_ok = define
  `(kara_quad_ok ([]:(int128#int128#int128#int128)list) <=> T) /\
   (kara_quad_ok (CONS (input,h_tw,hk,h) qrest) <=>
     h_tw = byteswap128 h /\
     word_subword hk (0,64):(64)word = karatsuba_mid h /\
     kara_quad_ok qrest)`;;

let project_triples = define
  `(project_triples ([]:(int128#int128#int128#int128)list) = []:(int128#int128#int128)list) /\
   (project_triples (CONS (input,h_tw,hk,h) qrest) =
     CONS (input,h_tw,hk) (project_triples qrest))`;;

(* The inductive helper: under kara_quad_ok, kara_quad_pmul quads acc is acc
   XOR the packed kara_acc of the projected triples. *)
let KARA_ACC_PACK_HELPER = prove
 (`!quads (acc:256 word).
    kara_quad_ok quads
    ==>
    (let pl,ph,pm = kara_acc (project_triples quads)
                              (word 0:int128) (word 0:int128) (word 0:int128) in
     kara_quad_pmul quads acc = word_xor acc (pack_corrected pl ph pm))`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[kara_quad_ok; project_triples; kara_quad_pmul; kara_acc;
                LET_DEF; LET_END_DEF; pack_corrected;
                WORD_ZX_0; WORD_SHL_ZERO; WORD_XOR_0] THEN
    GEN_TAC THEN CONV_TAC WORD_BLAST;
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`input:int128`; `h_tw:int128`; `hk:int128`;
                        `h:int128`; `qrest:(int128#int128#int128#int128)list`] THEN
    DISCH_TAC THEN GEN_TAC THEN
    REWRITE_TAC[kara_quad_ok; kara_quad_pmul; project_triples;
                KARA_ACC_CONS_DESTR; WORD_XOR_0_LEFT; WORD_XOR_0] THEN
    STRIP_TAC THEN
    ONCE_REWRITE_TAC[KARA_ACC_FIRST] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `word_xor (acc:256 word)
                                          (word_pmul (input:int128) (h:int128):256 word)`) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    SPEC_TAC(`kara_acc (project_triples (qrest:(int128#int128#int128#int128)list))
                       (word 0:int128) (word 0:int128) (word 0:int128)`,
             `q:int128#int128#int128`) THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`pl':int128`; `ph':int128`; `pm':int128`] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPECL [`input:int128`; `h:int128`; `hk:int128`]
                 KARATSUBA_BLOCK_PACKS_TO_PMUL_CLEAN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM PACK_CORRECTED_XOR] THEN
    REWRITE_TAC[PACK_CORRECTED_XOR] THEN
    CONV_TAC WORD_RULE]);;

(* ============================================================================
   The GMULTn builder for the band proofs.

   `build_GMULTn_fast n` returns a pair (PACKn_ID, GMULTn_FULL_CORRECT_BA):
     - PACKn_ID               : decN_tL = XOR_k (word_pmul a_k b_k)  (256-bit)
     - GMULTn_FULL_CORRECT_BA : the machine's Karatsuba-limb byteform =
                                polyval_reduce_prop3 (XOR_k word_pmul a_k b_k)

   Method: prove `decN_tL = XOR_k dec1[k]` structurally by XOR-AC over opaque
   pmul atoms (`AC WORD_XOR_ACI`, no bit-blast; a direct WORD_RULE proof of
   the 256-bit identity does not scale with N), then fold each single-block
   `dec1[k]` to `word_pmul a_k b_k` by PMUL_KARATSUBA.  This is the shared
   GHASH-bridge multiply lemma of the 2..8-block bands.

   It needs PMUL_KARATSUBA (common/karatsuba_pmul.ml) and KARATSUBA_LIMBS
   (above); the shared Prop3 reduction lemma GMULT_REDUCE_PROP3 and its
   helper V0LO are proved here.
   ========================================================================= *)


(* XOR is associative and commutative; WORD_XOR_ACI is the rewrite set of the
   structural `decN_tL = XOR_k dec1[k]` normalization (opaque pmul atoms, no
   bit-blast). *)
let WORD_XOR_ACI = WORD_RULE
  `(!x y:N word. word_xor x y = word_xor y x) /\
   (!x y z:N word. word_xor (word_xor x y) z = word_xor x (word_xor y z)) /\
   (!x y z:N word. word_xor x (word_xor y z) = word_xor y (word_xor x z))`;;

(* Helper: the low 64-bit lane of v0 = word_join aa bb XOR wa.  It makes the
   `word_pmul _ W` atoms of GMULT and Prop3 syntactically identical; pmul is
   opaque to BITBLAST, so the wv-inputs must match before the lane blast. *)
let V0LO = prove(
  `!aa bb:64 word. !wa:int128.
     word_subword (word_xor (word_join aa bb:int128) wa) (0,64):64 word =
     word_xor bb (word_subword wa (0,64):64 word)`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

(* The shared Prop3 reduction: the GMULT/assembly W-reduction byteform over an
   abstract 256-bit accumulator t equals polyval_reduce_prop3 t.  aa/bb/cc/dd
   are t's four 64-bit lanes and w = 0xC200000000000000.  It serves every block
   count: an N-block group reduces its accumulated 256-bit sum once. *)
let GMULT_REDUCE_PROP3 = prove(
  `!t:256 word.
     let aa = word_subword t (0,64):64 word in
     let bb = word_subword t (64,64):64 word in
     let cc = word_subword t (128,64):64 word in
     let dd = word_subword t (192,64):64 word in
     let w = word 13979173243358019584:64 word in
     let wa:int128 = word_pmul aa w in
     let v0:int128 = word_xor (word_join aa bb) wa in
     let wv:int128 = word_pmul (word_subword v0 (0,64):64 word) w in
     word_xor wv (word_xor (byteswap128 v0) (word_join dd cc)) = polyval_reduce_prop3 t`,
  GEN_TAC THEN REWRITE_TAC[polyval_reduce_prop3; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[V0LO] THEN
  ABBREV_TAC `wa:int128 = word_pmul (word_subword (t:256 word) (0,64):64 word) (word 13979173243358019584:64 word)` THEN
  ABBREV_TAC `wv:int128 = word_pmul (word_xor (word_subword (t:256 word) (64,64):64 word) (word_subword (wa:int128) (0,64):64 word)) (word 13979173243358019584:64 word)` THEN
  REWRITE_TAC[byteswap128] THEN BITBLAST_TAC);;

let mk_sub v lo = mk_comb(mk_comb(`word_subword:int128->num#num->64 word`, v), mk_pair(mk_small_numeral lo,`64`));;
let blk_lo k =
  let a = mk_var(Printf.sprintf "a%d" k,`:int128`) and b = mk_var(Printf.sprintf "b%d" k,`:int128`) in
  mk_comb(mk_comb(`word_pmul:64 word->64 word->128 word`, mk_sub a 0), mk_sub b 0);;
let blk_hi k =
  let a = mk_var(Printf.sprintf "a%d" k,`:int128`) and b = mk_var(Printf.sprintf "b%d" k,`:int128`) in
  mk_comb(mk_comb(`word_pmul:64 word->64 word->128 word`, mk_sub a 64), mk_sub b 64);;
let blk_mid k =
  let a = mk_var(Printf.sprintf "a%d" k,`:int128`) and b = mk_var(Printf.sprintf "b%d" k,`:int128`) in
  let xa = mk_comb(mk_comb(`word_xor:64 word->64 word->64 word`, mk_sub a 0), mk_sub a 64) in
  let xb = mk_comb(mk_comb(`word_xor:64 word->64 word->64 word`, mk_sub b 0), mk_sub b 64) in
  let pmid = mk_comb(mk_comb(`word_pmul:64 word->64 word->128 word`, xa), xb) in
  let xor128 x y = mk_comb(mk_comb(`word_xor:128 word->128 word->128 word`,x),y) in
  xor128 (xor128 pmid (blk_lo k)) (blk_hi k);;
let xor_fold128 f n =
  let xs = map f (0--(n-1)) in
  let rec go = function [x] -> x | x::xs -> mk_comb(mk_comb(`word_xor:128 word->128 word->128 word`,x), go xs) | [] -> failwith "empty" in
  go xs;;
let mk_decN_tL n =
  let zx t = mk_comb(`word_zx:128 word->256 word`, t) in
  let shl t k = mk_comb(mk_comb(`word_shl:256 word->num->256 word`, t), mk_small_numeral k) in
  let xor256 x y = mk_comb(mk_comb(`word_xor:256 word->256 word->256 word`,x),y) in
  xor256 (xor256 (zx (xor_fold128 blk_lo n)) (shl (zx (xor_fold128 blk_mid n)) 64))
         (shl (zx (xor_fold128 blk_hi n)) 128);;
let blkvars n = List.concat (map (fun k -> [mk_var(Printf.sprintf "a%d" k,`:int128`); mk_var(Printf.sprintf "b%d" k,`:int128`)]) (0--(n-1)));;
let dec1_at k =
  subst [mk_var(Printf.sprintf "a%d" k,`:int128`),`a0:int128`;
         mk_var(Printf.sprintf "b%d" k,`:int128`),`b0:int128`] (mk_decN_tL 1);;
let xor256_fold ts = match ts with
  | x::r -> List.fold_left (fun a y->mk_comb(mk_comb(`word_xor:256 word->256 word->256 word`,a),y)) x r
  | []->failwith"";;
(* decN_tL = XOR_k dec1[k], structural XOR-AC (no bit-blast) *)
let build_SPLIT n =
  let lf = REWRITE_CONV[WORD_ZX_XOR; WORD_SHL_XOR] (mk_decN_tL n)
  and rf = REWRITE_CONV[WORD_ZX_XOR; WORD_SHL_XOR] (xor256_fold (map dec1_at (0--(n-1)))) in
  TRANS lf (TRANS (AC WORD_XOR_ACI (mk_eq(rhs(concl lf), rhs(concl rf)))) (SYM rf));;
let pack1_at k =
  let ak=mk_var(Printf.sprintf "a%d" k,`:int128`) and bk=mk_var(Printf.sprintf "b%d" k,`:int128`) in
  prove(mk_eq(dec1_at k, mk_comb(mk_comb(`word_pmul:int128->int128->256 word`,ak),bk)),
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REWRITE_RULE[LET_DEF;LET_END_DEF] PMUL_KARATSUBA] THEN
    REWRITE_TAC[WORD_ZX_XOR; WORD_SHL_XOR] THEN CONV_TAC WORD_RULE);;
let build_PACKn n =
  let split = build_SPLIT n in
  TRANS split (GEN_REWRITE_CONV ONCE_DEPTH_CONV (map pack1_at (0--(n-1))) (rhs(concl split)));;
let build_GMULTn_fast n =
  let pack_id = build_PACKn n in
  let tL = lhs(concl pack_id) in
  let gmr = REWRITE_RULE[REWRITE_RULE[LET_DEF;LET_END_DEF] KARATSUBA_LIMBS]
              (SPEC tL (REWRITE_RULE[LET_DEF;LET_END_DEF] GMULT_REDUCE_PROP3)) in
  (pack_id, GENL (blkvars n) (TRANS gmr (AP_TERM `polyval_reduce_prop3` pack_id)));;

(* ========================================================================= *)
(* AES-GCM counter-mode helpers (binary-agnostic spec layer).                *)
(*                                                                           *)
(* The counter core of the proof: the per-block counter increment of the     *)
(* kernel (gcm_ctr_inc), its lane-byte form (GCM_CTR_INC_LANES), the NIST SP *)
(* 800-38D inc32 and the byteswap bridge between them, and the counter       *)
(* iterator gcm_ctr_inc_iter, a definition, so that block k's counter        *)
(* composes in a recursion or an N-block induction.                          *)
(*                                                                           *)
(* This counter vocabulary is private, next to the shared ctr_block of       *)
(* aes_gcm_spec.ml, because gcm_ctr_inc is the update in exactly the form    *)
(* the simulation produces (rev32, add, rev32 on the top lane of the counter *)
(* register): the simulated postconditions of this proof are stated with     *)
(* gcm_ctr_inc and gcm_ctr_inc_iter (and with the proof's own gcm_ctr_add    *)
(* and gcm_ctr_raw).  Restating them would mean re-simulating; instead the   *)
(* exported theorems are moved to ctr_block nonce c by                       *)
(* GCM_CTR_INC_ITER_INC32 below and the bridges GCM_CTR_INC_ITER_CTR_BLOCK   *)
(* and GCM_CTR_INC_ITER_NIST_IVEC further down.                              *)
(* ========================================================================= *)


(* ========================================================================= *)
(* The AES-GCM counter increment (the kernel's rev32, add, rev32).           *)
(*                                                                           *)
(* gcm_ctr_inc ivec = ivec with its top 32-bit lane byte-reversed, +1, and   *)
(* byte-reversed back.                                                       *)
(* ========================================================================= *)

let gcm_ctr_inc = new_definition
 `gcm_ctr_inc (ivec:(128)word) : (128)word =
   word_insert ivec (96,32)
     (word_bytereverse
        (word_add (word_bytereverse
                     (word_subword ivec (96,32):(32)word))
                  (word 1:(32)word)))`;;

(* gcm_ctr_inc as the byte-level lane form the simulation produces: the top  *)
(* 32-bit lane is the byte-reversed top lane of ctr0 plus one, byte-reversed *)
(* back, and the low 96 bits are those of ctr0, all built from the 8-bit     *)
(* subwords of ctr0.  The proofs rewrite between gcm_ctr_inc ctr0 and this   *)
(* form; GCM_CTR_INC2..7_LANES and GCM_CTR_ADD_LANES are built from it.      *)
let GCM_CTR_INC_LANES = prove(
 `!ctr0:int128.
    gcm_ctr_inc ctr0 =
    word_join
    (word_join
     (word_join
      (word_join
       (word_subword
        (word_add
         (word_join
          (word_join (word_subword ctr0 (96,8):(8)word) (word_subword ctr0 (104,8):(8)word)
           :(16)word)
          (word_join (word_subword ctr0 (112,8):(8)word) (word_subword ctr0 (120,8):(8)word)
           :(16)word) :(32)word)
         (word 1:(32)word)) (0,8) :(8)word)
       (word_subword
        (word_add
         (word_join
          (word_join (word_subword ctr0 (96,8):(8)word) (word_subword ctr0 (104,8):(8)word)
           :(16)word)
          (word_join (word_subword ctr0 (112,8):(8)word) (word_subword ctr0 (120,8):(8)word)
           :(16)word) :(32)word)
         (word 1:(32)word)) (8,8) :(8)word) :(16)word)
      (word_join
       (word_subword
        (word_add
         (word_join
          (word_join (word_subword ctr0 (96,8):(8)word) (word_subword ctr0 (104,8):(8)word)
           :(16)word)
          (word_join (word_subword ctr0 (112,8):(8)word) (word_subword ctr0 (120,8):(8)word)
           :(16)word) :(32)word)
         (word 1:(32)word)) (16,8) :(8)word)
       (word_subword
        (word_add
         (word_join
          (word_join (word_subword ctr0 (96,8):(8)word) (word_subword ctr0 (104,8):(8)word)
           :(16)word)
          (word_join (word_subword ctr0 (112,8):(8)word) (word_subword ctr0 (120,8):(8)word)
           :(16)word) :(32)word)
         (word 1:(32)word)) (24,8) :(8)word) :(16)word) :(32)word)
     (word_join
      (word_join (word_subword ctr0 (88,8):(8)word) (word_subword ctr0 (80,8):(8)word) :(16)word)
      (word_join (word_subword ctr0 (72,8):(8)word) (word_subword ctr0 (64,8):(8)word) :(16)word)
      :(32)word) :(64)word)
    (word_join
     (word_join
      (word_join (word_subword ctr0 (56,8):(8)word) (word_subword ctr0 (48,8):(8)word) :(16)word)
      (word_join (word_subword ctr0 (40,8):(8)word) (word_subword ctr0 (32,8):(8)word) :(16)word)
      :(32)word)
     (word_join
      (word_join (word_subword ctr0 (24,8):(8)word) (word_subword ctr0 (16,8):(8)word) :(16)word)
      (word_join (word_subword ctr0 (8,8):(8)word) (word_subword ctr0 (0,8):(8)word) :(16)word)
      :(32)word) :(64)word) :(128)word`,
  GEN_TAC THEN REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;

(* ========================================================================= *)
(* The byteswap bridge from gcm_ctr_inc to NIST SP 800-38D inc32             *)
(* ========================================================================= *)

(* GCM_CTR_INC_INC32: the NIST inc32 and the kernel's gcm_ctr_inc are        *)
(* conjugate by a full 128-bit byte reversal.  inc32 increments the low 32   *)
(* bits of its argument (the NIST big-endian counter) and keeps the top 96;  *)
(* gcm_ctr_inc increments the top 32-bit lane read byte-reversed.  So        *)
(* gcm_ctr_inc x = word_bytereverse (inc32 (word_bytereverse x)).            *)
let GCM_CTR_INC_INC32 = prove
 (`!x:128 word. gcm_ctr_inc x = word_bytereverse (inc32 (word_bytereverse x))`,
  GEN_TAC THEN REWRITE_TAC[gcm_ctr_inc; inc32] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN BITBLAST_TAC);;

(* ========================================================================= *)
(* The counter iterator: block k's counter block is gcm_ctr_inc_iter k ctr0. *)
(* It is a definition, so that it composes in a recursion or an N-block      *)
(* induction; it equals ITER k gcm_ctr_inc, so the ITER lemmas apply.        *)
(* ========================================================================= *)

let gcm_ctr_inc_iter = define
 `gcm_ctr_inc_iter 0 (x:128 word) = x /\
  gcm_ctr_inc_iter (SUC k) (x:128 word) = gcm_ctr_inc (gcm_ctr_inc_iter k x)`;;

let GCM_CTR_INC_ITER_ITER = prove
 (`!k x:128 word. gcm_ctr_inc_iter k x = ITER k gcm_ctr_inc x`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[gcm_ctr_inc_iter; ITER]);;

(* The iterated NIST bridge: it lets the specification state block k's       *)
(* counter NIST-faithfully (ITER k inc32 over the byte-reversed ivec) while  *)
(* the proof folds the kernel's lanes with gcm_ctr_inc_iter.                 *)
let GCM_CTR_INC_ITER_INC32 = prove
 (`!k x:128 word.
     gcm_ctr_inc_iter k x = word_bytereverse (ITER k inc32 (word_bytereverse x))`,
  INDUCT_TAC THENL
   [REWRITE_TAC[gcm_ctr_inc_iter; ITER; WORD_BYTEREVERSE_BYTEREVERSE];
    ASM_REWRITE_TAC[gcm_ctr_inc_iter; ITER; GCM_CTR_INC_INC32;
                    WORD_BYTEREVERSE_BYTEREVERSE]]);;

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
needs "arm/proofs/utils/aes_xts_common.ml";;

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

(* ========================================================================= *)
(* Byte-list view of a block list, for a byte_list_at(out_p,len)             *)
(* postcondition, on the XTS substrate int128_to_bytes.                      *)
(* ========================================================================= *)

(* Flatten an int128 block list to a byte list (APPEND of int128_to_bytes),  *)
(* exactly the XTS APPEND-of-int128_to_bytes shape.                          *)
let int128_list_to_bytes = define
 `int128_list_to_bytes ([]:int128 list) : byte list = [] /\
  int128_list_to_bytes (CONS w ws) =
    APPEND (int128_to_bytes w) (int128_list_to_bytes ws)`;;

(* LENGTH of the flattened byte list = 16 * number of blocks.                *)
let LENGTH_INT128_TO_BYTES = prove
 (`!w:int128. LENGTH(int128_to_bytes w) = 16`,
  REWRITE_TAC[int128_to_bytes; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let LENGTH_INT128_LIST_TO_BYTES = prove
 (`!ws. LENGTH(int128_list_to_bytes ws) = 16 * LENGTH ws`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[int128_list_to_bytes; LENGTH; LENGTH_APPEND;
                  LENGTH_INT128_TO_BYTES] THEN ARITH_TAC);;

(* The aes_ctr output as a byte list (int128_list_to_bytes above).           *)
let aes_ctr_bytes = new_definition
 `aes_ctr_bytes (ctr0:int128) (pts:int128 list) (keys:int128 list) : byte list =
    int128_list_to_bytes (aes_ctr ctr0 pts keys)`;;

(* ========================================================================= *)
(* Byte-extraction sublemmas for the whole-block byte_list_at bridges of     *)
(* this proof: a bytes128 read seen as its 16 bytes8 reads, and byte i of an *)
(* int128 (or of a flattened int128 list) as a word_subword.                 *)
(* BYTES128_TO_BYTES8_THM itself is in aes_xts_common.ml.                    *)
(* ========================================================================= *)

let BYTES128_TO_BYTES8_0 =
  REWRITE_RULE[ADD_CLAUSES; WORD_ADD_0] (SPEC `0` BYTES128_TO_BYTES8_THM);;

let SUBWORD_BYTES_TO_INT128 = prove(
 `!b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 i. i < 16
   ==> word_subword (bytes_to_int128 [b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15]) (8*i,8):byte =
       EL i [b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`i:num`,`i:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[bytes_to_int128] THEN REWRITE_TAC EL_16_8_CLAUSES THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN CONV_TAC WORD_BLAST);;

let BYTE8_OF_BYTES128 = prove(
 `!p s i. i < 16 ==> read (memory :> bytes8 (word_add p (word i))) s =
                     word_subword (read (memory :> bytes128 p) s) (8*i,8)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [BYTES128_TO_BYTES8_0] THEN
  ASM_SIMP_TAC[SUBWORD_BYTES_TO_INT128] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`i:num`,`i:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC EL_16_8_CLAUSES THEN REWRITE_TAC[WORD_ADD_0]);;

let EL_INT128_TO_BYTES = prove(
 `!w i. i < 16 ==> EL i (int128_to_bytes w):byte = word_subword w (8*i,8)`,
  GEN_TAC THEN REWRITE_TAC[int128_to_bytes] THEN
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC EL_16_8_CLAUSES THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN REWRITE_TAC[]);;

(* num DIV/MOD step lemmas for the int128_list_to_bytes per-byte unfolding.  *)
let DIV16_STEP = prove
 (`!i. 16 <= i ==> i DIV 16 = SUC((i - 16) DIV 16)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `i = (i - 16) + 1 * 16` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[DIV_MULT_ADD; ARITH_EQ] THEN ARITH_TAC]);;

let MOD16_STEP = prove
 (`!i. 16 <= i ==> i MOD 16 = (i - 16) MOD 16`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `i MOD 16 = ((i - 16) + 1 * 16) MOD 16` SUBST1_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[MOD_MULT_ADD]]);;

(* byte i of the flattened block list = byte (i MOD 16) of block (i DIV 16). *)
let EL_INT128_LIST_TO_BYTES = prove
 (`!cts i. i < 16 * LENGTH cts
     ==> EL i (int128_list_to_bytes cts) =
         word_subword (EL (i DIV 16) cts) (8 * (i MOD 16), 8):byte`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; int128_list_to_bytes; MULT_CLAUSES] THENL
   [REWRITE_TAC[LT] THEN ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `LENGTH(int128_to_bytes h) = 16` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_INT128_TO_BYTES]; ALL_TAC] THEN
  ASM_CASES_TAC `i < 16` THENL
   [ASM_SIMP_TAC[EL_APPEND] THEN
    SUBGOAL_THEN `i DIV 16 = 0 /\ i MOD 16 = i`
      (fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th; EL; HD]) THENL
     [ASM_SIMP_TAC[DIV_LT; MOD_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_INT128_TO_BYTES];
    ASM_SIMP_TAC[EL_APPEND] THEN
    SUBGOAL_THEN `i - 16 < 16 * LENGTH(t:int128 list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `16 <= i` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[DIV16_STEP; MOD16_STEP; EL; TL]]);;

(* ========================================================================= *)
(* Generic GCM machinery (direction-agnostic).                               *)
(*                                                                           *)
(* Nothing from here to the decrypt-specific section below depends on the    *)
(* direction: it is word and SIMD algebra, the GHASH/Karatsuba bridge layer, *)
(* exec-parameterized steppers, and N-block byteform merge and close tactics *)
(* that would serve the encrypt kernels as well.                             *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* SIMD REV64 fold-back lemmas.  The ARM simulator expands REV64.16B into a  *)
(* 4-level nested word_join/word_subword byte tree (128->64->32->16->8).     *)
(* These lemmas collapse it back to word_reversefields 8 as soon as it       *)
(* appears, so the large byte tree never builds up.                          *)
(* ------------------------------------------------------------------------- *)

let REV64_LOWER_LANE = prove(
  `!(xi:(128)word).
    word_join
      (word_join (word_join (word_subword xi (0,8):(8)word) (word_subword xi (8,8):(8)word):(16)word)
                 (word_join (word_subword xi (16,8):(8)word) (word_subword xi (24,8):(8)word):(16)word):(32)word)
      (word_join (word_join (word_subword xi (32,8):(8)word) (word_subword xi (40,8):(8)word):(16)word)
                 (word_join (word_subword xi (48,8):(8)word) (word_subword xi (56,8):(8)word):(16)word):(32)word):(64)word =
    word_reversefields 8 (word_subword xi (0,64):(64)word)`,
  CONV_TAC WORD_BLAST);;

let REV64_UPPER_LANE = prove(
  `!(xi:(128)word).
    word_join
      (word_join (word_join (word_subword xi (64,8):(8)word) (word_subword xi (72,8):(8)word):(16)word)
                 (word_join (word_subword xi (80,8):(8)word) (word_subword xi (88,8):(8)word):(16)word):(32)word)
      (word_join (word_join (word_subword xi (96,8):(8)word) (word_subword xi (104,8):(8)word):(16)word)
                 (word_join (word_subword xi (112,8):(8)word) (word_subword xi (120,8):(8)word):(16)word):(32)word):(64)word =
    word_reversefields 8 (word_subword xi (64,64):(64)word)`,
  CONV_TAC WORD_BLAST);;

let REV64_128 = prove(
  `!(xi:(128)word).
    word_join
      (word_reversefields 8 (word_subword xi (64,64):(64)word))
      (word_reversefields 8 (word_subword xi (0,64):(64)word)):(128)word =
    word_subword (word_join (word_reversefields 8 xi:(128)word)
                            (word_reversefields 8 xi:(128)word):(256)word) (64,128)`,
  CONV_TAC WORD_BLAST);;

let WORD_SWAP_HALVES_INVOLUTION = prove(
  `!(a:(128)word).
    word_subword
      (word_join
        (word_subword (word_join a a:(256)word) (64,128):(128)word)
        (word_subword (word_join a a:(256)word) (64,128):(128)word):(256)word)
      (64,128):(128)word = a`,
  CONV_TAC WORD_BLAST);;

(* The tails compute Karatsuba middle terms with
   `ext vD.16b,vN.16b,vN.16b,#8`, which the stepper models on a 128-bit
   register as `word_subword (word_join vN vN:256 word) (64,128):128 word`
   (a rotation by 64).  Only lane 0 of such a result is read (by an
   `eor .8b` or a `pmull .1d`), that is the projection
   `word_subword (<ext form>) (0,64)`, which is the plain lane
   `word_subword vN (64,64)`, the value an `ins vD.d[0],vN.d[1]` would give.
   EXT8_LANE0_IS_SUBWORD_HI rewrites that composed projection, not the
   standalone register: that would also fire on the byteswap/REV64
   machinery, which uses the same word_subword (word_join a a) (64,128)
   shape.  So the bridges see plain lanes, and ABBREV_INNER_PMULS_TAC
   numbers the qq atoms as for the ins form.  This is the identity
   SJ_COLLAPSE of the band machinery further down, stated here so that the
   per-step normalizer GCM_SIMD_SIMPLIFY_CORE_TAC can use it. *)
let EXT8_LANE0_IS_SUBWORD_HI = prove(
  `!(w:(128)word).
    word_subword (word_subword (word_join w w:(256)word) (64,128):(128)word) (0,64):(64)word =
    word_subword w (64,64)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* Structural normalization lemmas for the GHASH bridge close (word_insert
   comes from an ins, mov vD.d[i], and the nested word_subword from an ext). *)
let WORD_INSERT_SUBWORD = prove(
  `(!x:int128 y:64 word. word_subword (word_insert x (0,64) y : int128) (64,64) : 64 word = word_subword x (64,64)) /\
   (!x:int128 y:64 word. word_subword (word_insert x (64,64) y : int128) (0,64) : 64 word = word_subword x (0,64)) /\
   (!x:int128 y:64 word. word_subword (word_insert x (0,64) y : int128) (0,64) : 64 word = y) /\
   (!x:int128 y:64 word. word_subword (word_insert x (64,64) y : int128) (64,64) : 64 word = y)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN BITBLAST_TAC);;

let WORD_SUBWORD_SUBWORD = prove(
  `(!x:int128. word_subword (word_subword x (0,128) : int128) (0,64) : 64 word = word_subword x (0,64)) /\
   (!x:int128. word_subword (word_subword x (0,128) : int128) (64,64) : 64 word = word_subword x (64,64)) /\
   (!x:int128. word_subword (word_subword x (64,128) : int128) (0,64) : 64 word = word_subword x (64,64)) /\
   (!x:int128. word_subword (word_subword x (0,64) : 64 word) (0,64) : 64 word = word_subword x (0,64))`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* GHASH bridge lemmas: helpers for showing that the Karatsuba + Prop3       *)
(* reduction the assembly computes equals the spec-level polyval_dot /       *)
(* ghash_polyval_acc, so that the symbolic Q19 result at the xi_p store can  *)
(* be bridged to the postcondition.                                          *)
(* ------------------------------------------------------------------------- *)

let KARATSUBA_LIMBS_LET = prove(
  `!(p_lo:int128) (p_hi:int128) (cross:int128).
   let t:(256)word = word_xor (word_xor (word_zx p_lo)
                                        (word_shl (word_zx cross) 64))
                              (word_shl (word_zx p_hi) 128) in
   word_subword t (0,64) : 64 word = word_subword p_lo (0,64) /\
   word_subword t (64,64) : 64 word = word_xor (word_subword p_lo (64,64))
                                               (word_subword cross (0,64)) /\
   word_subword t (128,64) : 64 word = word_xor (word_subword p_hi (0,64))
                                                (word_subword cross (64,64)) /\
   word_subword t (192,64) : 64 word = word_subword p_hi (64,64)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT CONJ_TAC THEN BITBLAST_TAC);;

let JOIN_SUBWORD_RULES = prove(
  `(!a b:64 word. word_subword (word_join a b : int128) (0,64) : 64 word = b) /\
   (!a b:64 word. word_subword (word_join a b : int128) (64,64) : 64 word = a)`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN BITBLAST_TAC);;

let GHASH_1BLOCK_CORRECT = prove(
  `!acc block h:int128.
    polyval_dot (word_xor acc block) h = ghash_polyval_acc h acc [block]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ghash_polyval_acc; polyval_dot]);;

let BYTESWAP128_INVOLUTION = prove(
  `!x:int128. byteswap128(byteswap128 x) = x`,
  GEN_TAC THEN REWRITE_TAC[byteswap128] THEN BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* A GHASH bridge helper lemma.                                              *)
(* ------------------------------------------------------------------------- *)

(* word_subword (word_insert x (0,64) y) (0,64) = word_subword y (0,64),     *)
(* which drops the leftover tag tree x from the Karatsuba cross-term of the  *)
(* GHASH byte form.                                                          *)
let INSERT_SUBWORD_KILL = prove(
  `!(x:(128)word) (y:(128)word).
     word_subword ((word_insert x (0,64) y):(128)word) (0,64):(64)word
     = word_subword y (0,64)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* Scalable (a)+(b) decomposition of the GHASH multiply+reduce bridge.       *)
(*                                                                           *)
(* The 8-way kernels accumulate the Karatsuba products of a group of up to 8 *)
(* blocks in Q17/Q18/Q19 and apply one shared Prop3 reduction per group.     *)
(* Factoring the bridge as (a)+(b) makes both pieces reusable at every block *)
(* count (1..8), composed with the list-generic GHASH_POLYVAL_ACC_BATCHED    *)
(* (common/polyval_ghash.ml):                                                *)
(*   (a) PMUL_KARATSUBA (common/karatsuba_pmul.ml): the per-block 3-pmull    *)
(*       (lo/hi/mid) byteform = word_pmul a b (the 256-bit product);         *)
(*   (b) GMULT_REDUCE_PROP3 (above): the assembly's W-reduction byteform     *)
(*       over an abstract 256-bit accumulator t = polyval_reduce_prop3 t.    *)
(* ------------------------------------------------------------------------- *)

(* The full GHASH multiply+reduce bridge: the byte-level Karatsuba/Prop3 the *)
(* assembly computes (the left-hand side, over 64-bit pmul limbs) equals the *)
(* spec-level polyval_dot.  Derived from (a) PMUL_KARATSUBA, (b)             *)
(* GMULT_REDUCE_PROP3 and KARATSUBA_LIMBS_LET (the lanes of word_pmul a b    *)
(* are the limbs), instead of a single monolithic BITBLAST.                  *)
let GMULT_FULL_CORRECT_BA = prove(
  `!a b:int128.
   let a_lo = word_subword a (0,64) : 64 word in
   let a_hi = word_subword a (64,64) : 64 word in
   let b_lo = word_subword b (0,64) : 64 word in
   let b_hi = word_subword b (64,64) : 64 word in
   let p_lo:int128 = word_pmul b_lo a_lo in
   let p_hi:int128 = word_pmul b_hi a_hi in
   let p_mid:int128 = word_pmul (word_xor b_lo b_hi) (word_xor a_lo a_hi) in
   let cross = word_xor (word_xor p_mid p_lo) p_hi in
   let bb = word_xor (word_subword p_lo (64,64) : 64 word)
                     (word_subword cross (0,64) : 64 word) in
   let cc = word_xor (word_subword p_hi (0,64) : 64 word)
                     (word_subword cross (64,64) : 64 word) in
   let aa = word_subword p_lo (0,64) : 64 word in
   let dd = word_subword p_hi (64,64) : 64 word in
   let w:64 word = word 13979173243358019584 in
   let wa:int128 = word_pmul aa w in
   let v0:int128 = word_xor (word_join aa bb) wa in
   let wv:int128 = word_pmul (word_subword v0 (0,64) : 64 word) w in
   let result:int128 = word_xor wv (word_xor (byteswap128 v0) (word_join dd cc)) in
   result = polyval_dot a b`,
  (* Compose (a)+(b):
       polyval_dot a b = polyval_reduce_prop3 (word_pmul a b)        [def];
       word_pmul a b = the Karatsuba 256-bit assembly K  [(a) PMUL_KARATSUBA];
       polyval_reduce_prop3 K = the W-reduction byteform over K's lanes
                                           [GSYM (b) GMULT_REDUCE_PROP3];
       K's lanes = the p_lo/cross/p_hi limbs           [KARATSUBA_LIMBS_LET];
     then the two byteforms are identical up to the pmul argument order
     [WORD_PMUL_SYM]. *)
  REPEAT GEN_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[polyval_dot] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
    [REWRITE_RULE[LET_DEF; LET_END_DEF] PMUL_KARATSUBA] THEN
  GEN_REWRITE_TAC RAND_CONV
    [GSYM (REWRITE_RULE[LET_DEF; LET_END_DEF] GMULT_REDUCE_PROP3)] THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF; LET_END_DEF] KARATSUBA_LIMBS_LET] THEN
  REWRITE_TAC[WORD_PMUL_SYM] THEN REFL_TAC);;

let SIMD_SIMPLIFY_RULES = [REV64_LOWER_LANE; REV64_UPPER_LANE; REV64_128];;

let SIMD_SIMPLIFY_ASSUM_TAC =
  RULE_ASSUM_TAC(fun th ->
    try REWRITE_RULE SIMD_SIMPLIFY_RULES th with _ -> th);;

(* ------------------------------------------------------------------------- *)
(* REV32 (vector) per-32-bit-lane reversefields bridge.                      *)
(*                                                                           *)
(* The ISA model (arm/proofs/instruction.ml) defines arm_REV32_VEC with      *)
(*   usimd4 (word_reversefields esize) n,                                    *)
(* so arm_REV32_VEC_ALT (its EXPAND_SIMD_RULE form) leaves, per 32-bit lane, *)
(*   word_reversefields esize (word_subword n (32k,32)).                     *)
(* WORD_SIMPLE_SUBWORD_CONV does not reduce through word_reversefields, so   *)
(* that wrapper stays stuck, and a later positional RAND_CONV lands on a     *)
(* non-combination and fails ("RAND_CONV: Not a combination").  The decoder  *)
(* only emits esize 8 or 16 (decode.ml: esize = 8 << size with size in       *)
(* {0,1}; sizes 2 and 3 are UNDEFINED), so the two per-lane rewrites below,  *)
(* typed at :(32)word so that they never touch the 64-bit-lane               *)
(* word_reversefields of REV64 above, cover every REV32 the decoder can      *)
(* produce and let the subword chain reduce fully to the word_join /         *)
(* word_subword byte form the bridges expect.                                *)
(* ------------------------------------------------------------------------- *)
let WORD_REVERSEFIELDS_8_32 = prove
 (`word_reversefields 8 (x:(32)word) =
     word_join
       (word_join (word_subword x (0,8):(8)word) (word_subword x (8,8):(8)word):(16)word)
       (word_join (word_subword x (16,8):(8)word) (word_subword x (24,8):(8)word):(16)word)`,
  CONV_TAC WORD_BLAST);;

let WORD_REVERSEFIELDS_16_32 = prove
 (`word_reversefields 16 (x:(32)word) =
     word_join (word_subword x (0,16):(16)word) (word_subword x (16,16):(16)word)`,
  CONV_TAC WORD_BLAST);;

(* Reduce the stuck per-lane word_reversefields first (this fires only on a  *)
(* concrete esize 8 or 16, which the decoder supplies), then run the normal  *)
(* subword collapse.  With the ORELSEC inside a single TOP_DEPTH_CONV, the   *)
(* conversion never fails, and on terms without a 32-bit-lane reversefields  *)
(* it is a no-op.                                                            *)
let REV32_LANE_SUBWORD_CONV =
  TOP_DEPTH_CONV
    (GEN_REWRITE_CONV I [WORD_REVERSEFIELDS_8_32; WORD_REVERSEFIELDS_16_32]
     ORELSEC WORD_SIMPLE_SUBWORD_CONV);;

(* Per-step SIMD simplifier core: fold REV64 trees, cancel double half-swaps,
   collapse the lane-0 projections of ext (EXT8_LANE0_IS_SUBWORD_HI) and
   normalize nested subwords, also through REV32 lanes.  It runs after each
   GHASH step, so that the terms stay small. *)
let GCM_SIMD_SIMPLIFY_CORE_TAC =
  SIMD_SIMPLIFY_ASSUM_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE [WORD_SWAP_HALVES_INVOLUTION; EXT8_LANE0_IS_SUBWORD_HI]) THEN
  RULE_ASSUM_TAC(fun th ->
    try CONV_RULE(RAND_CONV(REV32_LANE_SUBWORD_CONV)) th
    with _ -> th);;

(* The REV64 fold needs two passes: the first normalizes the nested
   word_subword tree, the second lets the REV64 lane rules (REV64_LOWER_LANE,
   REV64_UPPER_LANE, REV64_128) match.  Two passes reach a fixpoint on the
   terms of these proofs. *)
let GCM_SIMD_SIMPLIFY_TAC =
  GCM_SIMD_SIMPLIFY_CORE_TAC THEN GCM_SIMD_SIMPLIFY_CORE_TAC;;

(* Resolve conditional branches in PC hypotheses *)
let RESOLVE_BRANCH_TAC =
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_eq c && can (find_term is_cond) (rhs c) &&
       can (find_term (fun t -> name_of t = "PC")) (lhs c) then
      CONV_RULE(RAND_CONV(
        REWRITE_CONV[WORD_RULE `word_sub (word_sub (word_add (x:int64) (word a)) x) (word b) = word_sub (word a) (word b)`;
                     WORD_RULE `word_sub (word_add (x:int64) (word a)) x = word a`] THENC
        DEPTH_CONV WORD_NUM_RED_CONV THENC DEPTH_CONV NUM_RED_CONV THENC
        REWRITE_CONV[BIT_WORD; DIMINDEX_64] THENC NUM_REDUCE_CONV THENC
        REWRITE_CONV[bitval] THENC INT_REDUCE_CONV THENC
        REWRITE_CONV[TAUT `~T <=> F`; TAUT `~F <=> T`;
                     TAUT `F /\ p <=> F`; TAUT `T /\ p <=> p`;
                     TAUT `(F <=> F) <=> T`; TAUT `(T <=> T) <=> T`;
                     TAUT `(T <=> F) <=> F`; TAUT `(F <=> T) <=> F`] THENC
        REWRITE_CONV[COND_CLAUSES])) th
    else th);;

(* Step with branch resolution before each step *)
let ARM_STEPS_RESOLVE_TAC exec range =
  MAP_EVERY (fun n -> RESOLVE_BRANCH_TAC THEN ARM_STEPS_TAC exec [n]) (range);;

(* Straight-line steps that keep the earlier states (ARM_VSTEPS_TAC), each
   followed by the SIMD fold; no branch resolution.  Used for short windows of
   the band tails, such as the stores and the ext/rev64 pair after the GHASH
   bridge: earlier facts such as the GHASH accumulators (Q17/Q18/Q19) and the
   store read-backs stay, and the fold keeps the REV64 byte trees bounded. *)
let ARM_VSTEPS_FOLD_TAC exec range =
  MAP_EVERY (fun n -> ARM_VSTEPS_TAC exec [n] THEN GCM_SIMD_SIMPLIFY_TAC) (range);;

(* A stepper for the windows with the REV64s of GHASH: the single step and
   discard of ARM_STEPS_TAC with the SIMD fold before each discard.  Per step:
     ARM_VERBOSE_STEP_TAC  -- advance to state s<n>
     GCM_SIMD_SIMPLIFY_TAC -- fold the REV64 byte tree into Q19
     DISCARD_OLDSTATE_TAC  -- drop the reads of earlier states
     CLARIFY_TAC
   The fold has to come before the discard: it collapses the byte tree into
   the bounded GHASH accumulator term in Q19, which then survives the
   discard.  Discarding at every step keeps the assumption list short. *)
let ARM_STEPS_FOLD_DISCARD_TAC exec snums =
  MAP_EVERY
    (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN GCM_SIMD_SIMPLIFY_TAC THEN
              DISCARD_OLDSTATE_TAC s THEN CLARIFY_TAC)
    (statenames "s" snums);;

(* Discard the flag facts (read NF/ZF/CF/VF) but keep read PC, whose final
   value ENSURES_FINAL_STATE_TAC needs for the PC postcondition. *)
let DISCARD_COUNTER_ONLY_TAC =
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    let s = string_of_term(concl th) in
    try String.sub s 0 7 = "read NF" ||
        String.sub s 0 7 = "read ZF" ||
        String.sub s 0 7 = "read CF" ||
        String.sub s 0 7 = "read VF"
    with _ -> false)));;

(* ------------------------------------------------------------------------- *)
(* GHASH bridge close.  At the bridge state of a one-block tail the assembly *)
(* holds in Q19 the Karatsuba+Prop3 GHASH of word_xor (brev xi) (brev ct)    *)
(* with key byteswap128 h (the key table holds H twisted, and the GHASH key  *)
(* is byteswap128 (read htbl_p)).  GMULT_FULL_CORRECT_BA, with               *)
(*   b := byteswap128 h,                                                     *)
(* makes the lane operands match; the helpers below abbreviate the Karatsuba *)
(* pmul limbs to opaque atoms, merge atoms that are equal up to argument     *)
(* order (WORD_PMUL_SYM, the congruence PMUL_CONG_128), and leave a          *)
(* structural XOR/join/subword identity for the bit-blasting tactics.        *)
(* ------------------------------------------------------------------------- *)

let PMUL_CONG_128 = prove(
  `!a b c d:64 word. a = c /\ b = d ==> (word_pmul a b:int128) = word_pmul c d`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let SUBWORD_XOR_JOIN_DIST = prove(
  `(!x y:int128. word_subword (word_xor x y) (0,64) : 64 word =
      word_xor (word_subword x (0,64)) (word_subword y (0,64))) /\
   (!x y:int128. word_subword (word_xor x y) (64,64) : 64 word =
      word_xor (word_subword x (64,64)) (word_subword y (64,64))) /\
   (!a b:64 word. word_subword (word_join a b : int128) (0,64) : 64 word = b) /\
   (!a b:64 word. word_subword (word_join a b : int128) (64,64) : 64 word = a)`,
  REPEAT CONJ_TAC THEN TRY(REPEAT GEN_TAC) THEN BITBLAST_TAC);;

let SUBWORD0_LEMMAS = prove(
  `(word_subword (word 0:int128) (0,64):64 word = word 0) /\
   (word_subword (word 0:int128) (64,64):64 word = word 0)`,
  CONJ_TAC THEN BITBLAST_TAC);;

(* Abbreviate each innermost fully applied word_pmul to a fresh qqN:int128. *)
let ABBREV_INNER_PMULS_TAC : tactic = fun (asl,w) ->
  let is_pmul_app t = try let (h,args)=strip_comb t in
        fst(dest_const h)="word_pmul" && length args=2 with _ -> false in
  let pmuls = setify(find_terms is_pmul_app w) in
  let contains_pmul_strict t = exists (fun p -> p <> t &&
     (let rec occ u = u=p ||
        (match u with Comb(a,b)->occ a||occ b|Abs(_,b)->occ b|_->false) in occ t)) pmuls in
  let inner = filter (fun t -> not(contains_pmul_strict t)) pmuls in
  let allvars = itlist (fun (_,th) acc ->
        union (map (fun v -> fst(dest_var v)) (frees(concl th))) acc)
        asl (map (fun v -> fst(dest_var v)) (frees w)) in
  let used = ref allvars in
  let fresh () = let rec go i = let n = "qq"^string_of_int i in
                   if mem n !used then go (i+1) else (used := n :: !used; n) in go 0 in
  EVERY (map (fun t -> ABBREV_TAC (mk_eq(mk_var(fresh(), `:int128`), t))) inner) (asl,w);;

(* For each pair of pmul-atom definitions, try to prove the atoms equal (the
   same product up to argument order, by WORD_PMUL_SYM, with operands equal by
   WORD_BLAST) and rewrite to merge them. *)
let MERGE_PMUL_ATOMS_TAC : tactic = fun (asl,w) ->
  let is_pmul_app t = try let (h,a)=strip_comb t in
        fst(dest_const h)="word_pmul" && length a=2 with _ -> false in
  let defs = filter (fun (_,th) ->
        let c = concl th in is_eq c && is_var(rhs c) && is_pmul_app(lhs c)) asl in
  let rec allpairs2 = function [] -> []
    | x::xs -> (map (fun y -> (x,y)) xs) @ allpairs2 xs in
  let cand = filter (fun ((_,t1),(_,t2)) -> rhs(concl t1) <> rhs(concl t2)) (allpairs2 defs) in
  let rec chain = function
    | [] -> ALL_TAC
    | ((_,t1),(_,t2))::rest ->
        let v1 = rhs(concl t1) and v2 = rhs(concl t2) in
        let prover =
          EXPAND_TAC (fst(dest_var v1)) THEN EXPAND_TAC (fst(dest_var v2)) THEN
          ((MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST)
           ORELSE (GEN_REWRITE_TAC LAND_CONV [WORD_PMUL_SYM] THEN
                   MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST)) in
        (SUBGOAL_THEN (mk_eq(v1,v2)) (fun th -> REWRITE_TAC[th]) THENL [prover; chain rest])
        ORELSE chain rest in
  chain cand (asl,w);;

(* Half projection helpers for the lane-fold close. *)
let JOINMID = prove(
  `!q:int128. word_subword (word_join q q :(256)word) (64,128):int128 =
     word_join (word_subword q (0,64):64 word) (word_subword q (64,64):64 word)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;
let QQ0SPLIT = prove(
  `!q:int128. q = word_join (word_subword q (64,64):64 word) (word_subword q (0,64):64 word)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* ========================================================================= *)
(* N-block GHASH bridge infrastructure, used by the 2..8-block bands.        *)
(*                                                                           *)
(* Helper lemmas for the 2-product GHASH bridge (independent of the byte     *)
(* form, so they hold for either direction) and the pmul-atom merge tactics. *)
(* ========================================================================= *)

(* word_join lane split: reduces a 128-bit word_join equality to two 64-bit  *)
(* lane equalities (so the final close is two small flat XOR identities).    *)
let JOIN_EQ_SPLIT = prove(
  `!(a:(64)word) (b:(64)word) (c:(64)word) (d:(64)word).
     ((word_join a b:(128)word) = word_join c d) <=> (a = c /\ b = d)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(fun th ->
      MP_TAC(REWRITE_RULE[JOIN_SUBWORD_RULES]
        (BETA_RULE(AP_TERM `\x:(128)word. word_subword x (64,64):(64)word` th))) THEN
      MP_TAC(REWRITE_RULE[JOIN_SUBWORD_RULES]
        (BETA_RULE(AP_TERM `\x:(128)word. word_subword x (0,64):(64)word` th))) THEN
      MESON_TAC[]);
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Per-lane reversefields: word_reversefields 8 on a full int128 commutes    *)
(* with the 64-bit lane projection (with a lane swap).                       *)
let RF8_SUBWORD = prove(
  `(!x:int128. word_subword (word_reversefields 8 x) (0,64):64 word =
               word_reversefields 8 (word_subword x (64,64):64 word)) /\
   (!x:int128. word_subword (word_reversefields 8 x) (64,64):64 word =
               word_reversefields 8 (word_subword x (0,64):64 word))`,
  CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* Subword lane extraction through word_zx / word_shl of the 256-bit         *)
(* Karatsuba assembly (for a 64-bit source).                                 *)
let SUBW_ZX_256 = prove(
  `(!x:64 word. word_subword (word_zx x:256 word) (0,64):64 word = x) /\
   (!x:64 word. word_subword (word_zx x:256 word) (64,64):64 word = word 0) /\
   (!x:64 word. word_subword (word_zx x:256 word) (128,64):64 word = word 0) /\
   (!x:64 word. word_subword (word_zx x:256 word) (192,64):64 word = word 0)`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;
let SUBW_SHL64_256 = prove(
  `(!x:64 word. word_subword (word_shl (word_zx x:256 word) 64) (0,64):64 word = word 0) /\
   (!x:64 word. word_subword (word_shl (word_zx x:256 word) 64) (64,64):64 word = x) /\
   (!x:64 word. word_subword (word_shl (word_zx x:256 word) 64) (128,64):64 word = word 0) /\
   (!x:64 word. word_subword (word_shl (word_zx x:256 word) 64) (192,64):64 word = word 0)`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;
let SUBW_SHL128_256 = prove(
  `(!x:64 word. word_subword (word_shl (word_zx x:256 word) 128) (0,64):64 word = word 0) /\
   (!x:64 word. word_subword (word_shl (word_zx x:256 word) 128) (64,64):64 word = word 0) /\
   (!x:64 word. word_subword (word_shl (word_zx x:256 word) 128) (128,64):64 word = x) /\
   (!x:64 word. word_subword (word_shl (word_zx x:256 word) 128) (192,64):64 word = word 0)`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;
(* and for a 128-bit source (the qq atoms). *)
let SUBW_ZX128_256 = prove(
  `(!x:128 word. word_subword (word_zx x:256 word) (0,64):64 word = word_subword x (0,64)) /\
   (!x:128 word. word_subword (word_zx x:256 word) (64,64):64 word = word_subword x (64,64)) /\
   (!x:128 word. word_subword (word_zx x:256 word) (128,64):64 word = word 0) /\
   (!x:128 word. word_subword (word_zx x:256 word) (192,64):64 word = word 0)`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;
let SUBW_SHL64_128_256 = prove(
  `(!x:128 word. word_subword (word_shl (word_zx x:256 word) 64) (0,64):64 word = word 0) /\
   (!x:128 word. word_subword (word_shl (word_zx x:256 word) 64) (64,64):64 word = word_subword x (0,64)) /\
   (!x:128 word. word_subword (word_shl (word_zx x:256 word) 64) (128,64):64 word = word_subword x (64,64)) /\
   (!x:128 word. word_subword (word_shl (word_zx x:256 word) 64) (192,64):64 word = word 0)`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;
let SUBW_SHL128_128_256 = prove(
  `(!x:128 word. word_subword (word_shl (word_zx x:256 word) 128) (0,64):64 word = word 0) /\
   (!x:128 word. word_subword (word_shl (word_zx x:256 word) 128) (64,64):64 word = word 0) /\
   (!x:128 word. word_subword (word_shl (word_zx x:256 word) 128) (128,64):64 word = word_subword x (0,64)) /\
   (!x:128 word. word_subword (word_shl (word_zx x:256 word) 128) (192,64):64 word = word_subword x (64,64))`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;
let SUBW_XOR_256 = prove(
  `!x y:256 word. !lo. word_subword (word_xor x y) (lo,64):64 word =
     word_xor (word_subword x (lo,64)) (word_subword y (lo,64))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_SUBWORD_XOR]);;

(* Collapse a 64-bit lane of subword (subword (join a a) (64,128)) to a      *)
(* plain lane of a (this is the duplicated mid-half that the wv operand of   *)
(* the W-reduction produces).                                                *)
let SUBSUB_JOIN_DUP = prove(
  `(!a:128 word. word_subword (word_subword (word_join a a :256 word) (64,128) :128 word) (0,64) :64 word
                 = word_subword a (64,64)) /\
   (!a:128 word. word_subword (word_subword (word_join a a :256 word) (64,128) :128 word) (64,64) :64 word
                 = word_subword a (0,64))`,
  CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* Abbreviate every `word_subword (a:int128) (lo,64)` subterm in the goal to *)
(* a fresh 64-bit variable, so the residual is a flat word_xor identity over *)
(* 64-bit variables that WORD_BITWISE_TAC closes.                            *)
let ABBREV_ALL_SUBWORDS_TAC : tactic = fun (asl,w) ->
  let is_sw64 t = try fst(dest_const(rator(rator t)))="word_subword" &&
                      type_of t = `:(64)word` &&
                      type_of (rand(rator t)) = `:int128` with _->false in
  let sws = setify(find_terms is_sw64 w) in
  let used = ref 0 in
  let tac = itlist (fun t acc ->
      let n = !used in used := n+1;
      ABBREV_TAC (mk_eq(mk_var("zw"^string_of_int n,`:64 word`), t)) THEN acc)
    sws ALL_TAC in
  tac (asl,w);;

(* Fast closer for the operand-equality subgoal of a merge: flatten the      *)
(* 256-bit Karatsuba lanes to 64-bit lanes, abbreviate them, and close by    *)
(* WORD_BITWISE_TAC instead of a WORD_BLAST of the whole terms.              *)
let FAST_OPERAND_TAC : tactic =
  REWRITE_TAC[SUBW_XOR_256; SUBW_ZX_256; SUBW_SHL64_256; SUBW_SHL128_256;
              SUBW_ZX128_256; SUBW_SHL64_128_256; SUBW_SHL128_128_256] THEN
  REWRITE_TAC[WORD_XOR_0; SUBSUB_JOIN_DUP; WORD_SUBWORD_SUBWORD;
              JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  ABBREV_ALL_SUBWORDS_TAC THEN
  WORD_BITWISE_TAC;;

(* Targeted pmul-atom merge for the 2-block bridge: one structurally         *)
(* determined pair per call; FAST_OPERAND_TAC closes the operand equalities. *)
let MERGE_ONE_2BLK_TAC : tactic = fun (asl,w) ->
  let is_pmul t = try let (hd,a)=strip_comb t in fst(dest_const hd)="word_pmul" && length a=2 with _->false in
  let is_wordconst t = try is_comb t && fst(dest_const(rator t))="word" && is_numeral(rand t) with _->false in
  let is_keyvar n = String.length n>=2 && n.[0]='k' &&
                    (try let _ = int_of_string (String.sub n 1 (String.length n-1)) in true with _->false) in
  let goalvars = setify(map (fun t->fst(dest_var t))
    (find_terms (fun t->is_var t && type_of t=`:int128` &&
      (let n=fst(dest_var t) in String.length n>=2 && String.sub n 0 2="qq")) w)) in
  let defs = filter (fun (_,th)->let c=concl th in is_eq c && is_var(rhs c) &&
    is_pmul(lhs c) && mem (fst(dest_var(rhs c))) goalvars) asl in
  let fvnames t = sort (<) (filter (fun n -> not(is_keyvar n))
                              (map (fun v->fst(dest_var v)) (frees t))) in
  let lane_tag op2 =
    if is_comb op2 && is_comb(rator op2) &&
       (try fst(dest_const(rator(rator op2)))="word_subword" with _->false)
    then string_of_term(rand op2) else "X" in
  let info th =
    let p = lhs(concl th) in
    let (_,args) = strip_comb p in
    let op1 = el 0 args and op2 = el 1 args in
    (rhs(concl th), op2, (fvnames op1, fvnames op2, lane_tag op2)) in
  let items = map (fun (_,th)-> info th) defs in
  let rec find_pair = function
    | [] -> None
    | (v,op2,sg)::rest ->
        let cand =
          if is_wordconst op2
          then filter (fun (v2,op2b,_)-> v2<>v && is_wordconst op2b && op2b=op2) rest
          else filter (fun (v2,op2b,sg2)-> v2<>v && not(is_wordconst op2b) && sg2=sg) rest in
        (match cand with (v2,_,_)::_ -> Some(v,v2) | [] -> find_pair rest) in
  (match find_pair items with
  | None -> (fun _ -> failwith "MERGE_ONE_2BLK_TAC: nothing to merge")
  | Some(v1,v2) ->
      let close_op = FAST_OPERAND_TAC ORELSE CONV_TAC WORD_BLAST in
      SUBGOAL_THEN (mk_eq(v1,v2))
        (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th]))
       THENL [EXPAND_TAC(fst(dest_var v1)) THEN EXPAND_TAC(fst(dest_var v2)) THEN
              ((MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN close_op)
               ORELSE (GEN_REWRITE_TAC LAND_CONV [WORD_PMUL_SYM] THEN
                       MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN close_op));
              ALL_TAC]) (asl,w);;

(* Repeat the single-merge to a fixpoint. *)
let MERGE_2BLK_TAC : tactic = REPEAT MERGE_ONE_2BLK_TAC;;

(* ========================================================================= *)
(* GMULT2 fast-reduce bridge.  GMULT2_FULL_CORRECT_BA is the 2-block fused   *)
(* multiply+reduce: the assembly's byteform that XOR-accumulates two         *)
(* Karatsuba triples and then runs the shared W-reduction equals             *)
(*   polyval_reduce_prop3 (word_pmul a0 b0 XOR word_pmul a1 b1).             *)
(* It is built from PMUL_KARATSUBA and GMULT_REDUCE_PROP3 (the W-reduction   *)
(* is proved once), so the reduction is never re-blasted.  MERGE_2BLK_TAC    *)
(* reconciles the per-block operand transpose (rev64 and h on one side, brev *)
(* and byteswap128 on the other).                                            *)
(* ========================================================================= *)

(* GMULT2_FULL_CORRECT_BA: the 2-block fused multiply+reduce byteform =      *)
(* polyval_reduce_prop3 (word_pmul a0 b0 XOR word_pmul a1 b1), built by the  *)
(* GMULTn builder above.                                                     *)
let _, GMULT2_FULL_CORRECT_BA = build_GMULTn_fast 2;;

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

(* ========================================================================= *)
(* AES-256-GCM decryption: the whole-block output and GHASH specification.   *)
(*                                                                           *)
(* The kernel processes whole 16-byte blocks only, so these specifications   *)
(* read the input byte buffer `x` as its len DIV 16 whole blocks, and the    *)
(* proof uses them only at len = 16 * N, N >= 1.  Each band's readable       *)
(* wrapper states its postcondition as                                       *)
(*   gcm_dec_pt_bytes (16 * N) x ctr0 keys      (the output) and             *)
(*   gcm_dec_final_xi (16 * N) x xi h           (the tag),                   *)
(* with the block decomposition hidden.  The per-N unfold lemmas             *)
(* GCM_DEC_GHASH_BLOCKS_WHOLE_N and GCM_DEC_PT_BYTES_WHOLE_N (N = 1..8)      *)
(* rewrite these back to the explicit N-block list a band's body produces,   *)
(* so the wrappers need no simulation.                                       *)
(*                                                                           *)
(* Decryption differs from encryption only in what GHASH reads: output block *)
(* k is word_xor ciphertext_k keystream_k (aes_ctr above), while GHASH runs  *)
(* over the raw ciphertext blocks `bytes_to_int128 (SUB_LIST (16*k,16) x)`,  *)
(* not over the plaintext.                                                   *)
(*                                                                           *)
(* The vocabulary is that of the band theorems: the base counter `ctr0` (the *)
(* ivec), `aes256_encrypt` with `gcm_ctr_inc_iter`, the GHASH key            *)
(* `byteswap128 h`, and `word_bytereverse` per block (which is the same as   *)
(* word_reversefields 8 at :128).                                            *)
(* ========================================================================= *)


(* ----------------------------------------------------------------------------
   The int128 block-list view of a byte buffer: `m` consecutive 16-byte blocks
   starting at block index `i` (byte offset 16*i), each read as a big int128.
   ------------------------------------------------------------------------- *)
let gcm_dec_blocks_from = define
 `gcm_dec_blocks_from (i:num) 0 (x:byte list) : int128 list = [] /\
  gcm_dec_blocks_from (i:num) (SUC m) (x:byte list) =
    CONS (bytes_to_int128 (SUB_LIST (16 * i, 16) x))
         (gcm_dec_blocks_from (i + 1) m x)`;;

let LENGTH_GCM_DEC_BLOCKS_FROM = prove
 (`!m i x. LENGTH (gcm_dec_blocks_from i m x) = m`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[gcm_dec_blocks_from; LENGTH]);;

(* Head-step: peel the first block. *)
let GCM_DEC_BLOCKS_FROM_STEP = prove
 (`!m i x. gcm_dec_blocks_from i (SUC m) x =
           CONS (bytes_to_int128 (SUB_LIST (16 * i, 16) x))
                (gcm_dec_blocks_from (i + 1) m x)`,
  REWRITE_TAC[gcm_dec_blocks_from]);;

(* ----------------------------------------------------------------------------
   GHASH input block list (decrypt): the len DIV 16 whole blocks of the raw
   ciphertext input (encrypt GHASHes its output instead, the one genuine
   dec/enc difference).
   ------------------------------------------------------------------------- *)
let gcm_dec_ghash_blocks = new_definition
 `gcm_dec_ghash_blocks (len:num) (x:byte list) : int128 list =
    gcm_dec_blocks_from 0 (len DIV 16) x`;;

(* The final GHASH accumulator Xi written to xi_p: byte-reverse in, run
   ghash_polyval_acc over the byte-reversed block list keyed by byteswap128 h,
   byte-reverse out.  This is the xi_p postcondition of the band bodies. *)
let gcm_dec_final_xi = new_definition
 `gcm_dec_final_xi (len:num) (x:byte list) (xi:int128) (h:int128) : int128 =
    word_bytereverse
      (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
         (MAP word_bytereverse (gcm_dec_ghash_blocks len x)))`;;

(* ----------------------------------------------------------------------------
   Output plaintext byte buffer (decrypt): counter mode over the same whole
   input blocks (aes_ctr XORs the keystream onto the ciphertext, recovering
   the plaintext).
   ------------------------------------------------------------------------- *)
let gcm_dec_pt_bytes = new_definition
 `gcm_dec_pt_bytes (len:num) (x:byte list) (ctr0:int128) (keys:int128 list) : byte list =
    aes_ctr_bytes ctr0 (gcm_dec_blocks_from 0 (len DIV 16) x) keys`;;

(* ----------------------------------------------------------------------------
   Per-N unfold lemmas at len = 16*N, N = 1..8 (one per readable band
   theorem): the whole-buffer specs as the explicit N-block list
     [bytes_to_int128 (SUB_LIST (0,16) x); ...;
      bytes_to_int128 (SUB_LIST (16*(N-1),16) x)].
   ------------------------------------------------------------------------- *)
let gcm_dec_whole_blocks_tm n =
  mk_list(map (fun i -> subst [mk_small_numeral (16 * i),`ofs:num`]
                          `bytes_to_int128 (SUB_LIST (ofs,16) (x:byte list))`)
              (0--(n-1)), `:int128`);;

(* gcm_dec_blocks_from 0 ((16 * n) DIV 16) x -> the explicit n-block list. *)
let GCM_DEC_BLOCKS_FROM_UNFOLD_TAC n =
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC(map (num_CONV o mk_small_numeral) (rev (1--n))) THEN
  REWRITE_TAC[gcm_dec_blocks_from] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];;

let build_ghash_blocks_whole n =
  prove(mk_forall(`x:byte list`,
          mk_eq(list_mk_comb(`gcm_dec_ghash_blocks`,
                             [mk_small_numeral (16 * n); `x:byte list`]),
                gcm_dec_whole_blocks_tm n)),
        GEN_TAC THEN REWRITE_TAC[gcm_dec_ghash_blocks] THEN
        GCM_DEC_BLOCKS_FROM_UNFOLD_TAC n);;

let GCM_DEC_GHASH_BLOCKS_WHOLE_1 = build_ghash_blocks_whole 1;;
let GCM_DEC_GHASH_BLOCKS_WHOLE_2 = build_ghash_blocks_whole 2;;
let GCM_DEC_GHASH_BLOCKS_WHOLE_3 = build_ghash_blocks_whole 3;;
let GCM_DEC_GHASH_BLOCKS_WHOLE_4 = build_ghash_blocks_whole 4;;
let GCM_DEC_GHASH_BLOCKS_WHOLE_5 = build_ghash_blocks_whole 5;;
let GCM_DEC_GHASH_BLOCKS_WHOLE_6 = build_ghash_blocks_whole 6;;
let GCM_DEC_GHASH_BLOCKS_WHOLE_7 = build_ghash_blocks_whole 7;;
let GCM_DEC_GHASH_BLOCKS_WHOLE_8 = build_ghash_blocks_whole 8;;

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
needs "common/ghash_nist_bridge.ml";;

(* ------------------------------------------------------------------------- *)
(* Machine code (print_literal_from_elf "arm/aes_gcm/aes256_gcm_dec_alt.o")  *)
(* ------------------------------------------------------------------------- *)

let aes256_gcm_dec_alt_mc = define_assert_from_elf "aes256_gcm_dec_alt_mc"
  "arm/aes_gcm/aes256_gcm_dec_alt.o"
[
  0xd503245f;       (* arm_BTI *)
  0xb400b9e1;       (* arm_CBZ X1 (word 5948) *)
  0xf240183f;       (* arm_TST X1 (rvalue (word 127)) *)
  0x5400b9a1;       (* arm_BNE (word 5940) *)
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
  0x5400996d;       (* arm_BLE (word 4908) *)
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
  0x5400172c;       (* arm_BGT (word 740) *)
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
  0x540005ec;       (* arm_BGT (word 188) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea41c85;       (* arm_MOV_VEC Q5 Q4 128 *)
  0xf10140bf;       (* arm_CMP X5 (rvalue (word 80)) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea31c64;       (* arm_MOV_VEC Q4 Q3 128 *)
  0x4ea11c23;       (* arm_MOV_VEC Q3 Q1 128 *)
  0x540006ac;       (* arm_BGT (word 212) *)
  0xf10100bf;       (* arm_CMP X5 (rvalue (word 64)) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea41c85;       (* arm_MOV_VEC Q5 Q4 128 *)
  0x4ea11c24;       (* arm_MOV_VEC Q4 Q1 128 *)
  0x540007ac;       (* arm_BGT (word 244) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0xf100c0bf;       (* arm_CMP X5 (rvalue (word 48)) *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea11c25;       (* arm_MOV_VEC Q5 Q1 128 *)
  0x540008ac;       (* arm_BGT (word 276) *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0xf10080bf;       (* arm_CMP X5 (rvalue (word 32)) *)
  0x4ea11c26;       (* arm_MOV_VEC Q6 Q1 128 *)
  0x54000a0c;       (* arm_BGT (word 320) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea11c27;       (* arm_MOV_VEC Q7 Q1 128 *)
  0xf10040bf;       (* arm_CMP X5 (rvalue (word 16)) *)
  0x54000b6c;       (* arm_BGT (word 364) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x14000069;       (* arm_B (word 420) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x6e184312;       (* arm_EXT Q18 Q24 Q24 64 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0xce01752c;       (* arm_EOR3 Q12 Q9 Q1 Q29 *)
  0x4ef9e111;       (* arm_PMULL2_VEC Q17 Q8 Q25 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x0ef9e113;       (* arm_PMULL_VEC Q19 Q8 Q25 64 *)
  0x0ef2e372;       (* arm_PMULL_VEC Q18 Q27 Q18 64 *)
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

(* `|- LENGTH aes256_gcm_dec_alt_tmc = 5956`.  Most statements spell the code
   region in their nonoverlapping preconditions as
   `LENGTH aes256_gcm_dec_alt_tmc`; the small-path theorems WB_FUSED_1BLOCK to
   WB_FUSED_4BLOCK and some terms of the safety proof write the numeral 5956.
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

(* The 12-slot aws-lc key table as one predicate over the GHASH input key h
   (the slot values are the byteswapped polyval_dot powers and the packed
   Karatsuba mids).  Expand it (REWRITE_TAC[htable_mem_dec] + let_CONV) before
   stepping, so that the table loads resolve. *)
let htable_mem_dec = new_definition
 `htable_mem_dec (h:int128) (ptr:int64) (s:armstate) <=>
    let hb = byteswap128 h in
    let h2 = byteswap128 (polyval_dot hb hb) in
    let h3 = byteswap128 (polyval_dot (polyval_dot hb hb) hb) in
    let h4 = byteswap128 (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) in
    let h5 = byteswap128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) hb) in
    let h6 = byteswap128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) hb) hb) in
    let h7 = byteswap128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) hb) hb) hb) in
    let h8 = byteswap128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) hb) hb) hb) hb) in
    read (memory :> bytes128 ptr) s = h /\
    read (memory :> bytes128 (word_add ptr (word 16))) s =
      word_join (karatsuba_mid h2) (karatsuba_mid h) /\
    read (memory :> bytes128 (word_add ptr (word 32))) s = h2 /\
    read (memory :> bytes128 (word_add ptr (word 48))) s = h3 /\
    read (memory :> bytes128 (word_add ptr (word 64))) s =
      word_join (karatsuba_mid h4) (karatsuba_mid h3) /\
    read (memory :> bytes128 (word_add ptr (word 80))) s = h4 /\
    read (memory :> bytes128 (word_add ptr (word 96))) s = h5 /\
    read (memory :> bytes128 (word_add ptr (word 112))) s =
      word_join (karatsuba_mid h6) (karatsuba_mid h5) /\
    read (memory :> bytes128 (word_add ptr (word 128))) s = h6 /\
    read (memory :> bytes128 (word_add ptr (word 144))) s = h7 /\
    read (memory :> bytes128 (word_add ptr (word 160))) s =
      word_join (karatsuba_mid h8) (karatsuba_mid h7) /\
    read (memory :> bytes128 (word_add ptr (word 176))) s = h8`;;

(* ------------------------------------------------------------------------- *)
(* Shared band machinery: the KEEPGH stepper and the byte-reversed tag.      *)
(* ------------------------------------------------------------------------- *)

(* The tail's Karatsuba mids use ext vD.16b,vN.16b,vN.16b,#8 where AWS-LC's
   code uses ins vD.d[0],vN.d[1], and only lane 0 of the result is read (by
   an .8b eor or a .1d pmull).  The stepper models the ext as
   word_subword (word_join vN vN) (64,128), a rotation by 64 bits, and the
   per-step normalizer GCM_SIMD_SIMPLIFY_CORE_TAC folds its lane-0 projection
   back to the plain lane word_subword vN (64,64) (EXT8_LANE0_IS_SUBWORD_HI),
   so the tail bridges see the operand shapes of the ins form.
   AUTO_MERGE_MIDS_KM_TAC below pairs the mids of the N >= 3 bridges whatever
   their qq numbering. *)

(* The KEEPGH stepper: after each step, discard every fact about an older
   state except those that read the GHASH registers Q16-Q19. *)
let DISCARD_OLDSTATE_KEEPGH_TAC s =
  let v = mk_var(s,`:armstate`) in
  let rec unbound_statevars_of_read bound tm = match tm with
      Comb(Comb(Const("read",_),_),st) -> if mem st bound then [] else [st]
    | Comb(a,b) -> union (unbound_statevars_of_read bound a) (unbound_statevars_of_read bound b)
    | Abs(vv,t) -> unbound_statevars_of_read (vv::bound) t | _ -> [] in
  let rec mentions_ghreg t = match t with
      Comb(Comb(Const("read",_),cmp),_) ->
        (match cmp with Const(n,_) -> n="Q16"||n="Q17"||n="Q18"||n="Q19" | _ -> false)
    | Comb(a,b) -> mentions_ghreg a || mentions_ghreg b | Abs(_,t2) -> mentions_ghreg t2 | _ -> false in
  DISCARD_ASSUMPTIONS_TAC(fun thm ->
    if mentions_ghreg (concl thm) then false else
    let us = unbound_statevars_of_read [] (concl thm) in
    if us = [] || us = [v] then false else if not(mem v us) then true else true);;
(* The per-step normalizer of the KEEPGH stepper, for the GHASH multiply and
   reduction windows of the band tails.  It is one pass of the rewrites of
   GCM_SIMD_SIMPLIFY_CORE_TAC rather than the double pass of
   GCM_SIMD_SIMPLIFY_TAC (the second pass only matters for the block-boundary
   REV64 folds, which the Q19 bridge redoes), applied only to the Q-register
   reads and memoized in gcm_simd_kgh_tbl (GCM_SIMD_SIMPLIFY_MEMO_TAC below).
   WB_PREP_TAC clears the table (CLEAR_KEEPGH_MEMO_TAC) at the start of each
   tail proof. *)
let gcm_simd_kgh_tbl : (term,unit) Hashtbl.t = Hashtbl.create 4096;;
let CLEAR_KEEPGH_MEMO_TAC : tactic =
  fun (asl,w) -> Hashtbl.clear gcm_simd_kgh_tbl; ALL_TAC (asl,w);;
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

(* The tag load ld1/ext/rev64 leaves Q19 as word_join (reversefields lo)
   (reversefields hi) of xi; this is word_bytereverse xi, the form in which
   the GHASH accumulator closes against the postcondition. *)
let Q19_BREVXI = prove
 (`word_join (word_reversefields 8 (word_subword (xi:int128) (0,64):int64))
             (word_reversefields 8 (word_subword xi (64,64):int64)):int128 =
   word_bytereverse xi`,
  CONV_TAC WORD_BLAST);;

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

(* ========================================================================= *)
(* Band lemmas for the 3..8-block whole-blocks tails (bit_len = 128*N).      *)
(* ========================================================================= *)

(* ---- shared N>=3 band machinery ---- *)

let collect_pmuls p t = let rec collect t acc = let acc = if p t then t::acc else acc in
  match t with Comb(a,b)->collect a (collect b acc)|Abs(_,b)->collect b acc|_->acc in setify(collect t []);;
let isWpmul t = try fst(dest_const(repeat rator t))="word_pmul" && rand t=`word 13979173243358019584:64 word` with _->false;;
let SJ_COLLAPSE = prove
 (`!w:128 word. word_subword (word_subword (word_join w w:256 word) (64,128):128 word) (0,64):64 word
                = word_subword w (64,64)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;
let SJ_COLLAPSE2 = prove
 (`!w:128 word. word_subword (word_subword (word_join w w:256 word) (64,128):128 word) (64,64):64 word
                = word_subword w (0,64)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;
let word_xor_left_comm = WORD_RULE `word_xor (a:64 word) (word_xor b c) = word_xor b (word_xor a c)`;;
let xor_pair_comm = WORD_RULE `word_xor (a:64 word) b = word_xor b a`;;
let term_leq t1 t2 = String.compare (string_of_term t1) (string_of_term t2) <= 0;;
let rec bubble_conv tm = match tm with
  | Comb(Comb(Const("word_xor",_), a), b) ->
    (match b with
     | Comb(Comb(Const("word_xor",_), b1), _) ->
       if term_leq a b1 then AP_TERM (mk_comb(rator(rator tm), a)) (bubble_conv b)
       else let th1 = PART_MATCH lhs word_xor_left_comm tm in
         let new_rhs = rhs(concl th1) in TRANS th1 (AP_TERM (rator new_rhs) (bubble_conv (rand new_rhs)))
     | _ -> if term_leq a b then REFL tm else PART_MATCH lhs xor_pair_comm tm)
  | _ -> REFL tm;;
let rec bubble_sort_conv tm =
  let rec count_xors t = match t with Comb(Comb(Const("word_xor",_), _), r) -> 1 + count_xors r | _ -> 0 in
  let n = count_xors tm in
  let rec apply_n_times k acc = if k <= 0 then acc else apply_n_times (k-1) (TRANS acc (bubble_conv (rhs(concl acc)))) in
  apply_n_times n (REFL tm);;
let rec bubble_fix tm = let th = bubble_sort_conv tm in let r = rhs(concl th) in
  if r = tm then th else TRANS th (bubble_fix r);;
let LANE_FINISH_TAC : tactic =
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  CONV_TAC(RAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[SJ_COLLAPSE; SJ_COLLAPSE2] THEN REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(BINOP_CONV bubble_fix) THEN REFL_TAC;;
let WA_UNIFY_TAC : tactic = fun (asl,w) ->
  let l=lhs w and r=rhs w in
  let iswa t = isWpmul t && not(can (find_term (fun u->u<>t && isWpmul u)) (rand(rator t))) in
  let lwa=hd(collect_pmuls iswa l) and rwa=hd(collect_pmuls iswa r) in
  if lwa=rwa then ALL_TAC (asl,w) else
  let wa_eq = prove(mk_eq(rwa,lwa), MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_RULE) in
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [wa_eq] (asl,w);;
let WV_UNIFY_TAC : tactic = fun (asl,w) ->
  let l=lhs w and r=rhs w in
  let iswv t = isWpmul t && (can (find_term (fun u->u<>t && isWpmul u)) (rand(rator t))) in
  let lwv=hd(collect_pmuls iswv l) and rwv=hd(collect_pmuls iswv r) in
  if lwv=rwv then ALL_TAC (asl,w) else
  let in_eq = BITBLAST_RULE (mk_eq(rand(rator rwv), rand(rator lwv))) in
  let wv_eq = AP_THM (AP_TERM `word_pmul:64 word->64 word->128 word` in_eq) `word 13979173243358019584:64 word` in
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [wv_eq] (asl,w);;
let ABBREV_WAWV_TAC : tactic = fun (asl,w) ->
  let l=lhs w in
  let iswa t = isWpmul t && not(can (find_term (fun u->u<>t && isWpmul u)) (rand(rator t))) in
  let lwa=hd(collect_pmuls iswa l) in
  (ABBREV_TAC (mk_eq(`WAz:128 word`, lwa)) THEN
   (fun (asl,w) -> let l=lhs w in
     (match collect_pmuls isWpmul l with wv::_ -> ABBREV_TAC (mk_eq(`WVz:128 word`, wv)) | [] -> ALL_TAC) (asl,w)))
  (asl,w);;
let pmul_mult_hpow t =
  let m = rand t in
  if can(find_term(fun u->u=`h2:int128`)) m then "H2" else
  if can(find_term(fun u->u=`h3:int128`)) m then "H3" else
  if can(find_term(fun u->u=`h4:int128`)) m then "H4" else
  if can(find_term(fun u->u=`h5:int128`)) m then "H5" else
  if can(find_term(fun u->u=`h6:int128`)) m then "H6" else
  if can(find_term(fun u->u=`h7:int128`)) m then "H7" else
  if can(find_term(fun u->u=`h8:int128`)) m then "H8" else
  if can(find_term(fun u->u=`h:int128`)) m then "H1" else
  if can(find_term(fun u->u=`word 13979173243358019584:64 word`)) m then "W" else "?";;
let WB_MID_FIX = [WORD_SUBWORD_INSERT_INNER; WORD_SUBWORD_INSERT_OUTER; INSERT_SUBWORD_KILL;
                  WORD_INSERT_SUBWORD; JOINMID; JOIN_SUBWORD_RULES; RF8_SUBWORD;
                  WORD_SUBWORD_SUBWORD; WORD_SUBWORD_XOR];;
let POLYVAL_DOT_SYM = prove
 (`!a b:int128. polyval_dot a b = polyval_dot b a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[polyval_dot] THEN AP_TERM_TAC THEN
  REWRITE_TAC[WORD_PMUL_SYM]);;
let GCM_CTR_INC2_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc ctr0)`,
        subst [`word 2:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;
let _, GMULT3_FULL_CORRECT_BA = build_GMULTn_fast 3;;
let spec_to_byteform_wb3 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2] =
       polyval_reduce_prop3
        (word_xor
         (word_xor
          (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h3))
          (word_pmul (word_bytereverse cph1) (byteswap128 h2)))
         (word_pmul (word_bytereverse cph2) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`;
            `word_bytereverse cph2:int128`] GHASH_POLYVAL_ACC_3)] THEN
  SUBGOAL_THEN `polyval_dot (byteswap128 h) (polyval_dot (byteswap128 h) (byteswap128 h)) = byteswap128 h3`
    (fun th -> REWRITE_TAC[th]) THENL
  [ONCE_REWRITE_TAC[POLYVAL_DOT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* Shared merge machinery (MERGE_ANY_TAC, MERGE_QQPAIR_KM_TAC).  MERGE_2BLK_TAC
   pairs the qq atoms by taking the first candidate with a compatible
   signature; at N = 8 that greedy choice pairs machine-lo with spec-hi atoms
   and leaves atoms that cannot be merged.  MERGE_ONE_ANY_TAC uses the same
   pairing signature but tries every candidate pair (by FIRST, backtracking
   when the WORD_BLAST operand close fails), so a bad pick does not stick. *)

let MERGE_ONE_ANY_TAC : tactic = fun (asl,w) ->
  let is_pmul t = try let (hd,a)=strip_comb t in fst(dest_const hd)="word_pmul" && List.length a=2 with _->false in
  let is_wordconst t = try is_comb t && fst(dest_const(rator t))="word" && is_numeral(rand t) with _->false in
  let is_keyvar n = String.length n>=2 && n.[0]='k' &&
                    (try let _ = int_of_string (String.sub n 1 (String.length n-1)) in true with _->false) in
  let goalvars = setify(map (fun t->fst(dest_var t))
    (find_terms (fun t->is_var t && type_of t=`:int128` &&
      (let n=fst(dest_var t) in String.length n>=2 && String.sub n 0 2="qq")) w)) in
  let defs = List.filter (fun (_,th)->let c=concl th in is_eq c && is_var(rhs c) &&
    is_pmul(lhs c) && mem (fst(dest_var(rhs c))) goalvars) asl in
  let fvnames t = sort (<) (List.filter (fun n -> not(is_keyvar n))
                              (map (fun v->fst(dest_var v)) (frees t))) in
  let lane_tag op2 =
    if is_comb op2 && is_comb(rator op2) &&
       (try fst(dest_const(rator(rator op2)))="word_subword" with _->false)
    then string_of_term(rand op2) else "X" in
  let info th =
    let p = lhs(concl th) in
    let (_,args) = strip_comb p in
    let op1 = el 0 args and op2 = el 1 args in
    (rhs(concl th), op2, (fvnames op1, fvnames op2, lane_tag op2)) in
  let items = map (fun (_,th)-> info th) defs in
  let rec allpairs_acc = function
    | [] -> []
    | (v,op2,sg)::rest ->
        let cands =
          if is_wordconst op2
          then List.filter (fun (v2,op2b,_)-> v2<>v && is_wordconst op2b && op2b=op2) rest
          else List.filter (fun (v2,op2b,sg2)-> v2<>v && not(is_wordconst op2b) && sg2=sg) rest in
        (map (fun (v2,_,_) -> (v,v2)) cands) @ allpairs_acc rest in
  let pairs = allpairs_acc items in
  if pairs = [] then failwith "MERGE_ONE_ANY_TAC: nothing to merge" else
  let close_op = FAST_OPERAND_TAC ORELSE CONV_TAC WORD_BLAST in
  let cand_tac (v1,v2) =
    SUBGOAL_THEN (mk_eq(v1,v2))
      (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th]))
     THENL [EXPAND_TAC(fst(dest_var v1)) THEN EXPAND_TAC(fst(dest_var v2)) THEN
            ((MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN close_op)
             ORELSE (GEN_REWRITE_TAC LAND_CONV [WORD_PMUL_SYM] THEN
                     MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN close_op));
            ALL_TAC] in
  FIRST (map cand_tac pairs) (asl,w);;
let MERGE_ANY_TAC : tactic = REPEAT MERGE_ONE_ANY_TAC;;

(* Stepping machinery for the tails of bands 3..8.  Keeping all of Q16-Q19
   across the long stores window (ARM_STEPS_FOLD_KEEPGH_TAC) makes the per-step
   GCM_SIMD_SIMPLIFY pass rescan a growing set of assumptions, quadratic
   overall.  Instead the window is stepped keeping only the latest read Q18
   fact (the carried GHASH mid; the store readbacks carry themselves forward),
   which is then named midacc, and the bridge expands it once. *)
let DISCARD_OLDSTATE_KEEPQ18_TAC s =
  let v = mk_var(s,`:armstate`) in
  let rec unbound_statevars_of_read bound tm = match tm with
      Comb(Comb(Const("read",_),_),st) -> if mem st bound then [] else [st]
    | Comb(a,b) -> union (unbound_statevars_of_read bound a) (unbound_statevars_of_read bound b)
    | Abs(vv,t) -> unbound_statevars_of_read (vv::bound) t | _ -> [] in
  let rec mentions_q18 t = match t with
      Comb(Comb(Const("read",_),cmp),_) ->
        (match cmp with Const(n,_) -> n="Q18" | _ -> false)
    | Comb(a,b) -> mentions_q18 a || mentions_q18 b | Abs(_,t2) -> mentions_q18 t2 | _ -> false in
  DISCARD_ASSUMPTIONS_TAC(fun thm ->
    if mentions_q18 (concl thm) then false else
    let us = unbound_statevars_of_read [] (concl thm) in
    if us = [] || us = [v] then false else true);;
let state_num_of_q18_fact th =
  try let c = concl th in
      if not(is_eq c) then None else
      match lhs c with
        Comb(Comb(Const("read",_),Const("Q18",_)),Var(sn,_)) when String.length sn > 1 && sn.[0]='s' ->
          Some(int_of_string(String.sub sn 1 (String.length sn - 1)))
      | _ -> None
  with _ -> None;;
let DISCARD_STALE_Q18_TAC : tactic = fun (asl,w) ->
  let nums = List.filter_map (fun (_,th) -> state_num_of_q18_fact th) asl in
  match nums with
  | [] | [_] -> ALL_TAC (asl,w)
  | _ -> let mx = List.fold_left max 0 nums in
         DISCARD_ASSUMPTIONS_TAC (fun th ->
           match state_num_of_q18_fact th with
           | Some k -> k < mx
           | None -> false) (asl,w);;
(* The per-step normalizer here is the single pass GCM_SIMD_SIMPLIFY_CORE_TAC,
   not the double pass GCM_SIMD_SIMPLIFY_TAC: the second pass is a full
   traversal of the carried GHASH terms and only folds the fresh REV64 byte
   trees at the block boundaries, which the Q19 bridge redoes downstream
   (WORD_BYTEREVERSE_REVERSEFIELDS, RF8_SUBWORD). *)
let ARM_STEPS_FOLD_Q18LATEST_TAC exec snums =
  MAP_EVERY (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN GCM_SIMD_SIMPLIFY_CORE_TAC THEN
              DISCARD_STALE_Q18_TAC THEN DISCARD_OLDSTATE_KEEPQ18_TAC s THEN CLARIFY_TAC)
    (statenames "s" snums);;
(* The merge of two given qq atoms, with karatsuba_mid unfolded inside the
   closing WORD_BLAST: the midacc expansion exposes machine mids whose spec
   partners are still folded in karatsuba_mid. *)
let MERGE_QQPAIR_KM_TAC (n1:string) (n2:string) : tactic =
  SUBGOAL_THEN (mk_eq(mk_var(n1,`:128 word`), mk_var(n2,`:128 word`)))
    (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
  [EXPAND_TAC n1 THEN EXPAND_TAC n2 THEN REWRITE_TAC[karatsuba_mid] THEN
   ((MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN
     (CONV_TAC WORD_BLAST ORELSE (REWRITE_TAC WB_MID_FIX THEN CONV_TAC WORD_BLAST)))
    ORELSE (GEN_REWRITE_TAC LAND_CONV [WORD_PMUL_SYM] THEN
            MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN
            (CONV_TAC WORD_BLAST ORELSE (REWRITE_TAC WB_MID_FIX THEN CONV_TAC WORD_BLAST))));
   ALL_TAC];;
(* WA_UNIFY_TAC with BITBLAST_RULE in place of WORD_RULE, which overflows the
   stack on the larger wa inputs of the midacc bridges. *)
let WA_UNIFY_BB_TAC : tactic = fun (asl,w) ->
  let l=lhs w and r=rhs w in
  let iswa t = isWpmul t && not(can (find_term (fun u->u<>t && isWpmul u)) (rand(rator t))) in
  let lwa=hd(collect_pmuls iswa l) and rwa=hd(collect_pmuls iswa r) in
  if lwa=rwa then ALL_TAC (asl,w) else
  let in_eq = BITBLAST_RULE (mk_eq(rand(rator rwa), rand(rator lwa))) in
  let mult_eq = BITBLAST_RULE (mk_eq(rand rwa, rand lwa)) in
  let wa_eq = MATCH_MP (ISPECL [rand(rator rwa); rand rwa; rand(rator lwa); rand lwa] PMUL_CONG_128)
                (CONJ in_eq mult_eq) in
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [wa_eq] (asl,w);;

(* Name-agnostic pairing of the leftover Karatsuba-mid qq atoms.  The per-step
   normalizer (GCM_SIMD_SIMPLIFY_CORE_TAC with EXT8_LANE0_IS_SUBWORD_HI) folds
   the ext-form Karatsuba-mid lanes to the plain lanes, but the qq numbers
   ABBREV_INNER_PMULS_TAC assigns are not stable across bands.  So this pairs
   the leftover mid pmuls by H-power, which depends only on the key operand h2,
   h3, ... and not on the data-side ext form: after MERGE_ANY_TAC has merged
   everything it can, the only residual mismatch is a set of Karatsuba-mid qq
   atoms that occur only on the left-hand side against others that occur only
   on the right-hand side, and each left one merges with the right one of the
   same H-power (MERGE_QQPAIR_KM_TAC, which closes by WORD_BLAST and so does
   not depend on the form). *)
let AUTO_MERGE_MIDS_KM_TAC : tactic = fun (asl,w) ->
  let rec xleaves t = match t with
    | Comb(Comb(Const("word_xor",_),a),b) -> xleaves a @ xleaves b | _ -> [t] in
  let qqs_in t = setify(map (fun v->fst(dest_var v))
     (List.filter (fun v-> let n=fst(dest_var v) in String.length n>=2 && String.sub n 0 2="qq")
        (frees t))) in
  let hpow n = try let (_,th)=List.find(fun(_,th)->let c=concl th in
       is_eq c && is_var(rhs c) && fst(dest_var(rhs c))=n) asl in pmul_mult_hpow(lhs(concl th))
     with _->"?" in
  let ll = xleaves(lhs w) and rl = xleaves(rhs w) in
  let dl = subtract (setify ll) (setify rl) and dr = subtract (setify rl) (setify ll) in
  let lqq = subtract (setify(List.concat_map qqs_in dl)) (setify(List.concat_map qqs_in dr)) in
  let rqq = subtract (setify(List.concat_map qqs_in dr)) (setify(List.concat_map qqs_in dl)) in
  let used = ref [] in
  let pairs = List.filter_map (fun ln ->
     let hp = hpow ln in
     try let rn = List.find (fun rn -> not(mem rn !used) && hpow rn = hp) rqq in
         used := rn :: !used; Some(ln,rn)
     with _ -> None) lqq in
  (EVERY (map (fun (a,b) -> MERGE_QQPAIR_KM_TAC a b) pairs)) (asl,w);;

(* The midacc bridges can leave a stray zero limb in each 64-bit lane (the
   carried mid enters the reduction as word 0 XOR ...): LANE_FINISH_Z_TAC
   collapses it before the bubble sort, then finishes as LANE_FINISH_TAC. *)
let ZSUB0 = prove(`word_subword (word 0:int128) (0,64):64 word = word 0`, CONV_TAC WORD_BLAST);;
let ZSUB0b = prove(`word_subword (word 0:int128) (64,64):64 word = word 0`, CONV_TAC WORD_BLAST);;
let LANE_FINISH_Z_TAC : tactic =
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  CONV_TAC(RAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[SJ_COLLAPSE; SJ_COLLAPSE2] THEN REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[ZSUB0; ZSUB0b; WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  CONV_TAC(BINOP_CONV bubble_fix) THEN REFL_TAC;;

let GCM_CTR_INC3_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))`,
        subst [`word 3:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;
let _, GMULT4_FULL_CORRECT_BA = build_GMULTn_fast 4;;
let spec_to_byteform_wb4 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2; word_bytereverse cph3] =
       polyval_reduce_prop3
        (word_xor
         (word_xor
          (word_xor
           (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h4))
           (word_pmul (word_bytereverse cph1) (byteswap128 h3)))
          (word_pmul (word_bytereverse cph2) (byteswap128 h2)))
         (word_pmul (word_bytereverse cph3) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`;
            `word_bytereverse cph2:int128`; `word_bytereverse cph3:int128`] GHASH_POLYVAL_ACC_4)] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

let GCM_CTR_INC4_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)))`,
        subst [`word 4:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;
let _, GMULT5_FULL_CORRECT_BA = build_GMULTn_fast 5;;
let spec_to_byteform_wb5 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h5 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
         word_bytereverse cph3; word_bytereverse cph4] =
       polyval_reduce_prop3
        (word_xor
         (word_xor
          (word_xor
           (word_xor
            (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h5))
            (word_pmul (word_bytereverse cph1) (byteswap128 h4)))
           (word_pmul (word_bytereverse cph2) (byteswap128 h3)))
          (word_pmul (word_bytereverse cph3) (byteswap128 h2)))
         (word_pmul (word_bytereverse cph4) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`;
            `word_bytereverse cph2:int128`; `word_bytereverse cph3:int128`;
            `word_bytereverse cph4:int128`] GHASH_POLYVAL_ACC_5)] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* ========================================================================= *)
(* The 6-block band: GHASH_POLYVAL_ACC_6, GMULT6_FULL_CORRECT_BA and         *)
(* spec_to_byteform_wb6.  GHASH_POLYVAL_ACC_6 is proved from                 *)
(* GHASH_POLYVAL_ACC_BATCHED like the 4- and 5-block forms in the N-block    *)
(* GHASH Karatsuba layer above.                                              *)
(* ========================================================================= *)
let GHASH_POLYVAL_ACC_6 = prove
 (`!(h:int128) (a:int128) (p:int128) (q:int128) (r:int128) (s:int128) (t:int128) (u:int128).
    ghash_polyval_acc h a [p:int128; q; r; s; t; u] =
    polyval_reduce_prop3
      (word_xor
        (word_pmul (word_xor a p) (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h) : 256 word)
       (word_xor
        (word_pmul q (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) : 256 word)
       (word_xor
        (word_pmul r (polyval_dot (polyval_dot (polyval_dot h h) h) h) : 256 word)
       (word_xor
        (word_pmul s (polyval_dot (polyval_dot h h) h) : 256 word)
       (word_xor
        (word_pmul t (polyval_dot h h) : 256 word)
        (word_pmul u h : 256 word))))))`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`h:int128`; `[q:int128; r; s; t; u]`; `a:int128`; `p:int128`]
                GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide; h_power; ARITH; SUB_0] THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[num_CONV `5`; num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`; h_power]);;
let GCM_CTR_INC5_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))))`,
        subst [`word 5:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;
let _, GMULT6_FULL_CORRECT_BA = build_GMULTn_fast 6;;
let spec_to_byteform_wb6 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h5 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h6 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
         word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5] =
       polyval_reduce_prop3
        (word_xor
         (word_xor
          (word_xor
           (word_xor
            (word_xor
             (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h6))
             (word_pmul (word_bytereverse cph1) (byteswap128 h5)))
            (word_pmul (word_bytereverse cph2) (byteswap128 h4)))
           (word_pmul (word_bytereverse cph3) (byteswap128 h3)))
          (word_pmul (word_bytereverse cph4) (byteswap128 h2)))
         (word_pmul (word_bytereverse cph5) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`;
            `word_bytereverse cph2:int128`; `word_bytereverse cph3:int128`;
            `word_bytereverse cph4:int128`; `word_bytereverse cph5:int128`] GHASH_POLYVAL_ACC_6)] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* ========================================================================= *)
(* The 7-block band: GHASH_POLYVAL_ACC_7 (proved like GHASH_POLYVAL_ACC_6),  *)
(* GMULT7_FULL_CORRECT_BA and spec_to_byteform_wb7.                          *)
(* ========================================================================= *)
let GHASH_POLYVAL_ACC_7 = prove
 (`!(h:int128) (a:int128) (p:int128) (q:int128) (r:int128) (s:int128) (t:int128) (u:int128) (v:int128).
    ghash_polyval_acc h a [p:int128; q; r; s; t; u; v] =
    polyval_reduce_prop3
      (word_xor
        (word_pmul (word_xor a p) (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h) h) : 256 word)
       (word_xor
        (word_pmul q (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h) : 256 word)
       (word_xor
        (word_pmul r (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) : 256 word)
       (word_xor
        (word_pmul s (polyval_dot (polyval_dot (polyval_dot h h) h) h) : 256 word)
       (word_xor
        (word_pmul t (polyval_dot (polyval_dot h h) h) : 256 word)
       (word_xor
        (word_pmul u (polyval_dot h h) : 256 word)
        (word_pmul v h : 256 word)))))))`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`h:int128`; `[q:int128; r; s; t; u; v]`; `a:int128`; `p:int128`]
                GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide; h_power; ARITH; SUB_0] THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[num_CONV `6`; num_CONV `5`; num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`; h_power]);;
let GCM_CTR_INC6_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)))))`,
        subst [`word 6:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;
let _, GMULT7_FULL_CORRECT_BA = build_GMULTn_fast 7;;
let spec_to_byteform_wb7 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h5 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h6 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h7 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
         word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5;
         word_bytereverse cph6] =
       polyval_reduce_prop3
        (word_xor
         (word_xor
          (word_xor
           (word_xor
            (word_xor
             (word_xor
              (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h7))
              (word_pmul (word_bytereverse cph1) (byteswap128 h6)))
             (word_pmul (word_bytereverse cph2) (byteswap128 h5)))
            (word_pmul (word_bytereverse cph3) (byteswap128 h4)))
           (word_pmul (word_bytereverse cph4) (byteswap128 h3)))
          (word_pmul (word_bytereverse cph5) (byteswap128 h2)))
         (word_pmul (word_bytereverse cph6) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`;
            `word_bytereverse cph2:int128`; `word_bytereverse cph3:int128`;
            `word_bytereverse cph4:int128`; `word_bytereverse cph5:int128`;
            `word_bytereverse cph6:int128`] GHASH_POLYVAL_ACC_7)] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* ========================================================================= *)
(* The 8-block band: GHASH_POLYVAL_ACC_8 (proved like GHASH_POLYVAL_ACC_6),  *)
(* GMULT8_FULL_CORRECT_BA and spec_to_byteform_wb8.                          *)
(* ========================================================================= *)
let GHASH_POLYVAL_ACC_8 = prove
 (`!(h:int128) (a:int128) (p:int128) (q:int128) (r:int128) (s:int128) (t:int128) (u:int128) (v:int128) (w:int128).
    ghash_polyval_acc h a [p:int128; q; r; s; t; u; v; w] =
    polyval_reduce_prop3
      (word_xor
        (word_pmul (word_xor a p) (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h) h) h) : 256 word)
       (word_xor
        (word_pmul q (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h) h) : 256 word)
       (word_xor
        (word_pmul r (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h) : 256 word)
       (word_xor
        (word_pmul s (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) : 256 word)
       (word_xor
        (word_pmul t (polyval_dot (polyval_dot (polyval_dot h h) h) h) : 256 word)
       (word_xor
        (word_pmul u (polyval_dot (polyval_dot h h) h) : 256 word)
       (word_xor
        (word_pmul v (polyval_dot h h) : 256 word)
        (word_pmul w h : 256 word))))))))`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`h:int128`; `[q:int128; r; s; t; u; v; w]`; `a:int128`; `p:int128`]
                GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide; h_power; ARITH; SUB_0] THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[num_CONV `7`; num_CONV `6`; num_CONV `5`; num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`; h_power]);;
let GCM_CTR_INC7_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))))))`,
        subst [`word 7:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;
let _, GMULT8_FULL_CORRECT_BA = build_GMULTn_fast 8;;
let spec_to_byteform_wb8 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h5 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h6 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h7 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h8 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
         word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5;
         word_bytereverse cph6; word_bytereverse cph7] =
       polyval_reduce_prop3
        (word_xor
         (word_xor
          (word_xor
           (word_xor
            (word_xor
             (word_xor
              (word_xor
               (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h8))
               (word_pmul (word_bytereverse cph1) (byteswap128 h7)))
              (word_pmul (word_bytereverse cph2) (byteswap128 h6)))
             (word_pmul (word_bytereverse cph3) (byteswap128 h5)))
            (word_pmul (word_bytereverse cph4) (byteswap128 h4)))
           (word_pmul (word_bytereverse cph5) (byteswap128 h3)))
          (word_pmul (word_bytereverse cph6) (byteswap128 h2)))
         (word_pmul (word_bytereverse cph7) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`;
            `word_bytereverse cph2:int128`; `word_bytereverse cph3:int128`;
            `word_bytereverse cph4:int128`; `word_bytereverse cph5:int128`;
            `word_bytereverse cph6:int128`; `word_bytereverse cph7:int128`] GHASH_POLYVAL_ACC_8)] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* The band tails WB_TAIL_1_TAC .. WB_TAIL_8_TAC, from the seam pc+3824      *)
(* through the residue cascade (or the exact-8 drain), the GHASH multiply    *)
(* and reduction, the bridge and the stores to the core exit pc+4556.  Their *)
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
  (* the GHASH bridge at s341 (pc+4544, after eor v19,v19,v18) *)
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
  (* 344 = st1 {v19.16b},[x3] (tag store); exit at pc+4556 *)
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
  (* the GMULT2 bridge at s355 (pc+4544, after eor v19,v19,v18) *)
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
  (* 358 = st1 {v19.16b},[x3] (tag store); exit at pc+4556 *)
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
     L256_dec_exact8_drain (0x11e4..0x1360) instead of the residue cascade,
     which only r = 1..7 enter.  The drain folds three block pairs with eor3
     (the first block of each pair parks its products in v13/v14/v15, which
     are added into the accumulators together with the second block's) and
     rejoins the shared reduction at 0x1194 (L256_dec_epilogue) with a b;
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



(* ------------------------------------------------------------------------- *)
(* The shared front WB_FRONT_BUF of bands 5..8: its statement and the term   *)
(* builders of the simulated postconditions.                                 *)
(* ------------------------------------------------------------------------- *)

(* ---- the and-mask on the 5..8 front: 16 * nblk - 1 rounded down to a
   multiple of 128 is 0 for 1 <= nblk <= 8 (AND_MASK_16NBLK_ANY states it for
   any nblk). ---- *)
let AND_MASK_16NBLK = prove
 (`!nblk. 1 <= nblk /\ nblk <= 8
        ==> word_and (word_sub (word (16 * nblk)) (word 1))
                     (word 18446744073709551488):int64 = word 0`,
  GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `1 <= n /\ n <= 8 <=>
    n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV);;

(* The input buffer as whole blocks: for a 16 * n-byte prefix of x, block k < n
   is the bytes128 read at in_p + 16 * k (by induction on n, with
   READ_BYTES_AND_BYTE128_MERGE of aes_xts_common.ml). *)
let INPUT_BYTES_TO_BYTE128_LANES = prove
 (`!n (in_p:int64) (x:byte list) s.
    16 * n <= LENGTH x /\
    read (memory :> bytes (in_p, 16 * n)) s = num_of_bytelist (SUB_LIST (0, 16 * n) x)
    ==> !k. k < n ==> read (memory :> bytes128 (word_add in_p (word (16 * k)))) s =
                      bytes_to_int128 (SUB_LIST (16 * k, 16) x)`,
  INDUCT_TAC THENL [REWRITE_TAC[LT]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`in_p:int64`; `16 * n`; `x:byte list`; `s:armstate`] READ_BYTES_AND_BYTE128_MERGE) THEN
  ANTS_TAC THENL [REWRITE_TAC[ARITH_RULE `16 * n + 16 = 16 * SUC n`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL [REWRITE_TAC[ARITH_RULE `16 * n + 16 = 16 * SUC n`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[LT] THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`in_p:int64`; `x:byte list`; `s:armstate`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[]]);;

(* The statement of WB_FRONT_BUF.  Its postcondition wb_front_postcond (below)
   is the simulated state s273 at the seam, with the 8 in-flight keystream
   towers folded to aes13; it is built with term builders, so that the front is
   simulated only in the proof. *)

let wb_front_pre_tm = `\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
          read PC s = word (pc + 0x1c) /\ read SP s = stackpointer /\
          C_ARGUMENTS [in_p; word (128 * nblk); out_p; xi_p; ivec_p; key_p; htbl_p] s /\
          read (memory :> bytes (in_p, 16 * nblk)) s = num_of_bytelist ibytes /\
          read (memory :> bytes128 xi_p) s = xi /\
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
          htable_mem_dec h htbl_p s`;;

let wb_front_frame_tm = `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(out_p:int64, 16 * nblk); memory :> bytes(xi_p:int64, 16);
                 memory :> bytes(ivec_p:int64, 16); memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31]`;;

(* The band 5 <= nblk <= 8: WB_FRONT_BUF, stated with these hypotheses, is used
   only by prove_band for bands 5..8 (bands 1..4 take the b.le at step 8 to the
   small-message path and are proved by WB_FUSED_1BLOCK .. WB_FUSED_4BLOCK).
   The bands supply nblk = 5..8, so 5 <= nblk closes by NUM_REDUCE_CONV, and
   the union band wbn_front_hyps_uni_tm also starts with 5 <= nblk. *)
let wb_front_hyps_tm = `5 <= nblk /\ nblk <= 8 /\ LENGTH (ibytes:byte list) = 16 * nblk /\
    aligned 16 stackpointer /\
    nonoverlapping (word pc, LENGTH aes256_gcm_dec_alt_tmc) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, LENGTH aes256_gcm_dec_alt_tmc) (out_p:int64, 16 * nblk) /\
    nonoverlapping (word pc, LENGTH aes256_gcm_dec_alt_tmc) (xi_p:int64, 16) /\
    nonoverlapping (word pc, LENGTH aes256_gcm_dec_alt_tmc) (ivec_p:int64, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 16 * nblk) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 240) /\
    nonoverlapping (ivec_p, 16) (htbl_p:int64, 192) /\
    nonoverlapping (in_p, 16 * nblk) (stackpointer, 80) /\
    nonoverlapping (key_p, 240) (stackpointer, 80) /\
    nonoverlapping (htbl_p, 192) (stackpointer, 80) /\
    nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
    nonoverlapping (xi_p, 16) (in_p, 16 * nblk) /\
    nonoverlapping (xi_p, 16) (key_p, 240) /\
    nonoverlapping (xi_p, 16) (htbl_p, 192) /\
    nonoverlapping (xi_p, 16) (stackpointer, 80)`;;

let wb_front_vars = [`pc:num`;`stackpointer:int64`;`out_p:int64`;`xi_p:int64`;`ivec_p:int64`;
            `in_p:int64`;`key_p:int64`;`htbl_p:int64`;`nblk:num`;`ibytes:byte list`;
            `xi:int128`;`ctr0:int128`;`k0:int128`;`k1:int128`;`k2:int128`;`k3:int128`;
            `k4:int128`;`k5:int128`;`k6:int128`;`k7:int128`;`k8:int128`;`k9:int128`;
            `k10:int128`;`k11:int128`;`k12:int128`;`k13:int128`;`k14:int128`;`h:int128`];;

let mk_wb_front_goal postcond =
  let ens = subst [wb_front_pre_tm,`PPP:armstate->bool`; postcond,`QQQ:armstate->bool`;
                   wb_front_frame_tm,`CCC:armstate->armstate->bool`]
              `ensures arm PPP QQQ CCC` in
  list_mk_forall(wb_front_vars, mk_imp(wb_front_hyps_tm, ens));;

(* gcm_ctr_inc^k ctr0 for k = 1..7, as the lanes the counter setup of the
   front computes (GCM_CTR_INC_LANES to GCM_CTR_INC7_LANES). *)
let wb_ctr_lanes_thms =
  [GCM_CTR_INC_LANES; GCM_CTR_INC2_LANES; GCM_CTR_INC3_LANES; GCM_CTR_INC4_LANES;
   GCM_CTR_INC5_LANES; GCM_CTR_INC6_LANES; GCM_CTR_INC7_LANES];;
(* The simulated postconditions (wb_front_postcond and the others built below)
   state the 8 in-flight keystream towers folded to aes13 (gcm_ctr_inc^i ctr0)
   k0 .. k13, which keeps the Q-register conjuncts readable; wb_front_fold_tac
   applies the same folds, GSYM aes13 and the GSYM of the lane lemmas, to the
   simulated assumptions before the final-state match. *)
let wb_front_fold_tac =
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM aes13]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE(map GSYM wb_ctr_lanes_thms));;
(* The raw counter accumulator kept in v30, machine-level vocabulary like
   gcm_ctr_inc (no exported statement mentions it): the counter block
   byte-grouped as rev32 reads it, with w added to its top 32-bit lane.
   rev32 of it is gcm_ctr_add w ctr0, the AES input block for counter w, and
   add v30.4s,v30.4s,v31.4s (v31 = word 2^96) takes gcm_ctr_raw w ctr0 to
   gcm_ctr_raw (word_add w (word 1)) ctr0.  It is defined here because
   wb_front_postcond below states Q30 with it; its lane lemmas (SUBW_RAW_*,
   GCM_CTR_RAW_INCR) come with the counter algebra below and its fold tactics
   (REV32_FOLD_TAC, CTR_RAW_INCR_FOLD_TAC) with the main-loop proof. *)
let gcm_ctr_raw_def = new_definition
 `gcm_ctr_raw (w:32 word) (ctr0:int128) : int128 =
   word_join
    (word_join
      (word_add
        (word_join
          (word_join (word_subword ctr0 (96,8):8 word) (word_subword ctr0 (104,8):8 word):16 word)
          (word_join (word_subword ctr0 (112,8):8 word) (word_subword ctr0 (120,8):8 word):16 word):32 word)
        w)
      (word_join (word_join (word_subword ctr0 (64,8):8 word) (word_subword ctr0 (72,8):8 word):16 word)
        (word_join (word_subword ctr0 (80,8):8 word) (word_subword ctr0 (88,8):8 word):16 word):32 word):64 word)
    (word_join
      (word_join (word_join (word_subword ctr0 (32,8):8 word) (word_subword ctr0 (40,8):8 word):16 word)
        (word_join (word_subword ctr0 (48,8):8 word) (word_subword ctr0 (56,8):8 word):16 word):32 word)
      (word_join (word_join (word_subword ctr0 (0,8):8 word) (word_subword ctr0 (8,8):8 word):16 word)
        (word_join (word_subword ctr0 (16,8):8 word) (word_subword ctr0 (24,8):8 word):16 word):32 word):64 word):int128`;;

(* ---- term builders for the simulated postconditions ----------------------
   wb_front_postcond (below), wbn_front_prebranch_postcond,
   wbn_front_prefix_postcond, wbn_front_postcond_i0 and
   wbn_prepretail_post_raw each describe the final state of a simulation (of
   the front, the shared prefix or the prepretail): the aligned_bytes_loaded
   fact and every `read _ sN = _` assumption (folded by wb_front_fold_tac),
   with sN abstracted to s, in the order the simulator leaves them.  They are
   built from the term families below. *)

(* h-power towers: dot j = polyval_dot^(j-1) over byteswap128 h *)
let rec hdot j = if j = 1 then `byteswap128 h`
  else mk_comb(mk_comb(`polyval_dot:int128->int128->int128`, hdot (j-1)), `byteswap128 h`);;
(* counter i: gcm_ctr_inc^i ctr0 *)
let mk_ctr i =
  let rec go n = if n = 0 then `ctr0:int128`
    else mk_comb(`gcm_ctr_inc`, go (n-1)) in go i;;
(* input block i as the 128-bit lane the kernel loads *)
let mk_cph i = subst [mk_small_numeral(16*i),`nnn:num`]
  `bytes_to_int128 (SUB_LIST (nnn,16) (ibytes:byte list))`;;

(* the conjunct `read c s = v`, and the postcondition \s. c1 /\ ... /\ cn *)
let wbp_rd c v = mk_eq(list_mk_icomb "read" [c; `s:armstate`], v);;
let wbp_post cs = mk_abs(`s:armstate`, list_mk_conj cs);;
(* the keystream tower aes13 ctr k0 .. k13 *)
let wbp_aes13 ctr =
  list_mk_comb(`aes13`, ctr :: map (fun i -> mk_var("k"^string_of_int i,`:int128`)) (0--13));;
(* htable_mem_dec slot values: H^j (h itself for j = 1), and the packed
   karatsuba mids of H^(j+1) and H^j *)
let wbp_hpow j = if j = 1 then `h:int128` else mk_comb(`byteswap128`, hdot j);;
let wbp_hmid j = mk_comb(mk_comb(`word_join:int64->int64->int128`,
  mk_comb(`karatsuba_mid`, wbp_hpow (j+1))), mk_comb(`karatsuba_mid`, wbp_hpow j));;
(* read (memory :> bytes128 (base + 16 * i)) s *)
let wbp_mem128 base i =
  let addr = if i = 0 then base
    else subst [base,`bbb:int64`; mk_small_numeral(16*i),`nnn:num`] `word_add bbb (word nnn):int64` in
  subst [addr,`aaa:int64`] `read (memory :> bytes128 (aaa:int64)) s:int128`;;
(* the round keys k0 .. k14 and the 12 htable_mem_dec slots as memory reads *)
let wbp_key_reads =
  map (fun i -> mk_eq(wbp_mem128 `key_p:int64` i, mk_var("k"^string_of_int i,`:int128`))) (0--14);;
let wbp_htable_reads =
  conjuncts(rhs(concl((REWRITE_CONV[htable_mem_dec] THENC TOP_DEPTH_CONV let_CONV)
    `htable_mem_dec h htbl_p s`)));;
(* NZCV after cmp a, #n and after cmp a, b *)
let wbp_cmpi_flags a n = map (subst [a,`aaa:int64`; mk_small_numeral n,`nnn:num`])
  [`read NF s <=> ival (word_sub aaa (word nnn):int64) < &0`;
   `read ZF s <=> val (word_sub aaa (word nnn):int64) = 0`;
   `read CF s <=> nnn <= val (aaa:int64)`;
   `read VF s <=> ~(ival (aaa:int64) - &nnn = ival (word_sub aaa (word nnn):int64))`];;
let wbp_cmp_flags a b = map (subst [a,`aaa:int64`; b,`bbb:int64`])
  [`read NF s <=> ival (word_sub aaa bbb:int64) < &0`;
   `read ZF s <=> val (word_sub aaa bbb:int64) = 0`;
   `read CF s <=> val (bbb:int64) <= val (aaa:int64)`;
   `read VF s <=> ~(ival (aaa:int64) - ival (bbb:int64) = ival (word_sub aaa bbb:int64))`];;
(* the raw counter words: wbp_bytes4 x [a;b;c;d] joins the bytes of x at bit
   offsets a, b, c, d; wbp_lane b is the 32-bit lane of ctr0 at bit b, grouped
   as gcm_ctr_raw groups it, and wbp_revlane b the same bytes reversed *)
let wbp_bytes4 x offs =
  let byte k = mk_comb(mk_icomb(`word_subword:A word->num#num->8 word`, x),
                       mk_pair(mk_small_numeral k, `8`)) in
  let j16 a b = mk_comb(mk_comb(`word_join:8 word->8 word->16 word`, a), b)
  and j32 a b = mk_comb(mk_comb(`word_join:16 word->16 word->32 word`, a), b) in
  match map byte offs with
    [a;b;c;d] -> j32 (j16 a b) (j16 c d)
  | _ -> failwith "wbp_bytes4";;
let wbp_lane b = wbp_bytes4 `ctr0:int128` [b; b+8; b+16; b+24];;
let wbp_revlane b = wbp_bytes4 `ctr0:int128` [b+24; b+16; b+8; b];;
let wbp_add32 x n = mk_comb(mk_comb(`word_add:32 word->32 word->32 word`, x),
                            mk_comb(`word:num->32 word`, mk_small_numeral n));;
let wbp_join128 a b c d =
  let j64 x y = mk_comb(mk_comb(`word_join:32 word->32 word->64 word`, x), y) in
  mk_comb(mk_comb(`word_join:64 word->64 word->128 word`, j64 a b), j64 c d);;
(* v30 after the front's adds: top lane + w, then + 1, the other lanes + 0 *)
let wbp_raw_acc w =
  wbp_join128 (wbp_add32 (wbp_add32 (wbp_lane 96) w) 1) (wbp_add32 (wbp_lane 64) 0)
              (wbp_add32 (wbp_lane 32) 0) (wbp_add32 (wbp_lane 0) 0);;
(* rev32 of the raw counter with top lane + w: the AES input for counter w *)
let wbp_rev_ctr w =
  wbp_join128 (wbp_bytes4 (wbp_add32 (wbp_lane 96) w) [0; 8; 16; 24])
              (wbp_revlane 64) (wbp_revlane 32) (wbp_revlane 0);;
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
   `read X3 s = xi_p`;
   `read X6 s = htbl_p`;
   `read (memory :> bytes (in_p,16 * nblk)) s = num_of_bytelist ibytes`;
   `read (memory :> bytes128 xi_p) s = xi`;
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

(* ========================================================================= *)
(* The shared front prefix: the entry pc+0x1c to the 0x448 b.ge (pc+1096),   *)
(* steps 1..267, proved once (WBN_FRONT_PREBRANCH) for the front of bands    *)
(* 5..8 (WB_FRONT_BUF) and the front of the >=9 bands (WBN_FRONT_PREFIX).    *)
(*                                                                           *)
(* It loads ivec, the tag and the 15 round keys, computes the 8 counter      *)
(* blocks and runs the 8 keystream towers up to the final aese (aes13); it   *)
(* reads no input block and no key-table entry, and its one data-dependent   *)
(* branch, the dispatch b.le at step 8, falls through for nblk >= 5.  So it  *)
(* is proved on the union band 5 <= nblk /\ 128 * nblk < 2 EXP 64, with X5   *)
(* kept general by the _ANY mask lemmas and the raw NF/VF/ZF/CF facts of the *)
(* cmp x0,x5 kept.  Each consumer then chains a short leg by                 *)
(* ENSURES_TRANS_SIMPLE: WB_FRONT_BUF takes the 0x448 b.ge in the 5..8 band  *)
(* and runs steps 268..273 to the seam s273; WBN_FRONT_PREFIX falls through  *)
(* in the >=9 band and runs steps 268..295 to s295.                          *)
(*                                                                           *)
(* The helpers below (state_num_of_read_q30, DISCARD_STALE_Q30_TAC and the   *)
(* _ANY mask lemmas) also serve the nblk >= 9 fronts, including the 9..16    *)
(* leg (WBN_FRONT_TO_PREP_916).                                              *)
(* ========================================================================= *)

(* keep only the latest read Q30 fact *)
let state_num_of_read_q30 th =
  let c = concl th in
  try (match lhs c with
       | Comb(Comb(Const("read",_),q),st) when string_of_term q = "Q30" ->
           let s = fst(dest_var st) in
           if String.length s > 1 && s.[0] = 's'
           then int_of_string (String.sub s 1 (String.length s - 1)) else (-1)
       | _ -> (-1))
  with _ -> (-1);;
let DISCARD_STALE_Q30_TAC : tactic = fun (asl,w) ->
  let nums = List.filter (fun n -> n >= 0)
    (List.map (fun (_,th) -> state_num_of_read_q30 th) asl) in
  if nums = [] then ALL_TAC (asl,w) else
  let mx = itlist max nums (-1) in
  DISCARD_ASSUMPTIONS_TAC (fun th ->
    let n = state_num_of_read_q30 th in n >= 0 && n < mx) (asl,w);;

(* the two nblk-dependent scalar values, for any nblk:
   x9 = len_bits >> 3 = 16 * nblk (USHR_128NBLK_ANY) and
   x5 = (x9 - 1) AND -128 = 128 * ((nblk - 1) DIV 8) (AND_MASK_16NBLK_ANY) *)
let USHR_128NBLK_ANY = prove
 (`!nblk. 128 * nblk < 2 EXP 64
        ==> word_ushr (word (128 * nblk):int64) 3 = word (16 * nblk)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ushr] THEN
  ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN AP_TERM_TAC THEN ARITH_TAC);;
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

(* d = 128 * ((nblk - 1) DIV 8) = 0 for 1 <= nblk <= 8, so X5 = in_p and the
   <=8 band takes the b.ge to the tail *)
let D_ZERO_LE8 = prove
 (`!nblk. 1 <= nblk /\ nblk <= 8 ==> 128 * ((nblk - 1) DIV 8) = 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(nblk - 1) DIV 8 = 0` (fun th -> REWRITE_TAC[th; MULT_CLAUSES]) THEN
  MATCH_MP_TAC DIV_LT THEN ASM_ARITH_TAC);;

(* The dispatch cmp x9,#0x40 ; b.le to the small-message path at 0x34/0x38   *)
(* (front steps 7, 8), with x9 = word (16 * nblk) from the lsr x9,x1,#3: for *)
(* nblk >= 5 the b.le falls through (16 * nblk >= 80 > 64) and the front     *)
(* runs on; nblk <= 4 takes the small-message path (WB_FUSED_kBLOCK).        *)
(* GUARD_LE_FALLTHRU resolves the branch condition for 5 <= nblk, by         *)
(* arithmetic on word (16 * nblk) alone; the prefix stepper adds it to the   *)
(* assumptions before stepping 7--8, so that the stepper folds the branch to *)
(* the fall-through.                                                         *)
let GUARD_LE_FALLTHRU = prove
 (`!nblk. 5 <= nblk /\ 16 * nblk < 2 EXP 63
      ==> (~(~(val (word_sub (word (16 * nblk):int64) (word 64)) = 0) /\
             (ival (word_sub (word (16 * nblk):int64) (word 64)) < &0 <=>
              ~(ival (word (16 * nblk):int64) - &64 =
                ival (word_sub (word (16 * nblk):int64) (word 64))))) <=> F)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_sub (word (16 * nblk):int64) (word 64) = word(16 * nblk - 64)`
    SUBST1_TAC THENL
   [MP_TAC(SPECL [`16 * nblk`; `64`] (INST_TYPE[`:64`,`:N`] WORD_SUB)) THEN
    ASM_SIMP_TAC[ARITH_RULE `5 <= nblk ==> 64 <= 16 * nblk`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[IVAL_WORD_SMALL;
               ARITH_RULE `16 * nblk < 2 EXP 63 ==> 16 * nblk - 64 < 2 EXP 63`] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `(16 * nblk - 64) MOD 2 EXP 64 = 16 * nblk - 64` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
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

(* The union hypotheses contain 5 <= nblk but not 1 <= nblk
   (wbn_front_hyps_uni_tm above), so ASSUME `1 <= nblk` would add a
   hypothesis that is not in the goal, and the justification of the
   enclosing SUBGOAL_THEN would fail (Failure "ABS").  So this tactic keeps
   only the assumptions 5 <= nblk and 128 * nblk < 2 EXP 64, from which
   ARITH_TAC derives the bounds needed by USHR_128NBLK_ANY,
   AND_MASK_16NBLK_ANY and INPUT_BYTES_TO_BYTE128_LANES. *)
let NBLK_ARITH_UNI_TAC =
  MP_TAC(ASSUME `5 <= nblk`) THEN MP_TAC(ASSUME `128 * nblk < 2 EXP 64`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;;

let WBN_FRONT_PREP_BUF_UNI_TAC =
  SUBGOAL_THEN `SUB_LIST (0, 16 * nblk) (ibytes:byte list) = ibytes` ASSUME_TAC THENL
   [MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes128 in_p) s0 = bytes_to_int128 (SUB_LIST (0,16) ibytes)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `s0:armstate`] INPUT_BYTES_TO_BYTE128_LANES) THEN
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
   `read X3 s = xi_p`;
   `read X6 s = htbl_p`;
   `read (memory :> bytes (in_p,16 * nblk)) s = num_of_bytelist ibytes`;
   `read (memory :> bytes128 xi_p) s = xi`;
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

(* ---- buffer-form band statements ---------------------------------------- *)
let mk_outp_read i =
  let addr = if i = 0 then `out_p:int64`
    else subst [mk_small_numeral(16*i),`nnn:num`] `word_add out_p (word nnn):int64` in
  subst [addr,`aaa:int64`] `read (memory :> bytes128 (aaa:int64)) s:int128`;;
let mk_out_conj i =
  mk_eq(mk_outp_read i,
    subst [mk_cph i,`ccc:int128`; mk_ctr i,`ttt:int128`]
      `word_xor (ccc:int128) (aes256_encrypt (ttt:int128)
        [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`);;
let mk_ghash_list k =
  mk_flist(map (fun i -> mk_comb(`word_bytereverse:int128->int128`, mk_cph i)) (0--(k-1)));;

(* The band-exit counter write-back conjunct in spine form,
   read [ivec_p] = gcm_ctr_inc_iter k ctr0, used by mk_band_goal and closed
   by WB_IVEC_CLOSE_TAC in the band tails. *)
let mk_ivec_conj k = subst [mk_small_numeral k,`kkk:num`]
    `read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter kkk ctr0`;;

let mk_band_goal k =
  let n16 = mk_small_numeral(16*k) and n128 = mk_small_numeral(128*k) in
  let hyps = subst [n16,`sss:num`]
    `LENGTH (ibytes:byte list) = sss /\
     aligned 16 stackpointer /\
     nonoverlapping (word pc, LENGTH aes256_gcm_dec_alt_tmc) (stackpointer:int64, 80) /\
     nonoverlapping (word pc, LENGTH aes256_gcm_dec_alt_tmc) (out_p:int64, sss) /\
     nonoverlapping (word pc, LENGTH aes256_gcm_dec_alt_tmc) (xi_p:int64, 16) /\
     nonoverlapping (word pc, LENGTH aes256_gcm_dec_alt_tmc) (ivec_p:int64, 16) /\
     nonoverlapping (out_p, sss) (xi_p, 16) /\
     nonoverlapping (out_p, sss) (ivec_p, 16) /\
     nonoverlapping (xi_p, 16) (ivec_p, 16) /\
     nonoverlapping (ivec_p, 16) (in_p:int64, sss) /\
     nonoverlapping (ivec_p, 16) (key_p:int64, 240) /\
     nonoverlapping (ivec_p, 16) (htbl_p:int64, 192) /\
     nonoverlapping (in_p, sss) (stackpointer, 80) /\
     nonoverlapping (key_p, 240) (stackpointer, 80) /\
     nonoverlapping (htbl_p, 192) (stackpointer, 80) /\
     nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
     nonoverlapping (xi_p, 16) (in_p, sss) /\
     nonoverlapping (xi_p, 16) (key_p, 240) /\
     nonoverlapping (xi_p, 16) (htbl_p, 192) /\
     nonoverlapping (xi_p, 16) (stackpointer, 80) /\
     nonoverlapping (out_p, sss) (in_p, sss) /\
     nonoverlapping (out_p, sss) (key_p, 240) /\
     nonoverlapping (out_p, sss) (htbl_p, 192) /\
     nonoverlapping (out_p, sss) (stackpointer, 80)` in
  let pre = subst [n16,`sss:num`; n128,`bbb:num`]
    `\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
        read PC s = word (pc + 0x1c) /\ read SP s = stackpointer /\
        C_ARGUMENTS [in_p; word bbb; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
        read (memory :> bytes (in_p, sss)) s = num_of_bytelist ibytes /\
        read (memory :> bytes128 xi_p) s = xi /\
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
        htable_mem_dec h htbl_p s` in
  let pc_post = `read PC s = word (pc + 4556)` in
  let x9_post = subst [n16,`sss:num`] `read X9 s = word sss` in
  let outs = map mk_out_conj (0--(k-1)) in
  let xi_post = subst [mk_ghash_list k,`lll:int128 list`]
    `read (memory :> bytes128 xi_p) s =
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
     MAYCHANGE [memory :> bytes(out_p:int64, sss); memory :> bytes(xi_p:int64, 16);
                memory :> bytes(ivec_p:int64, 16);
                memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
     MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31]` in
  let ens = subst [pre,`PPP:armstate->bool`; post,`QQQ:armstate->bool`;
                   frame,`CCC:armstate->armstate->bool`] `ensures arm PPP QQQ CCC` in
  let vars = subtract wb_front_vars [`nblk:num`] in
  list_mk_forall(vars, mk_imp(hyps, ens));;

(* ---- recomposition machinery -------------------------------------------- *)
let arith_16k k = ARITH_RULE(mk_eq(mk_binop `( * ):num->num->num` `16` (mk_small_numeral k),
                                   mk_small_numeral(16*k)));;
let arith_128k k = ARITH_RULE(mk_eq(mk_binop `( * ):num->num->num` `128` (mk_small_numeral k),
                                    mk_small_numeral(128*k)));;
(* front lemma instantiated at nblk:=k, arithmetic normalized *)
let wbf_at k = REWRITE_RULE[arith_16k k; arith_128k k]
  (SPECL [`pc:num`;`stackpointer:int64`;`out_p:int64`;`xi_p:int64`;`ivec_p:int64`;
          `in_p:int64`;`key_p:int64`;`htbl_p:int64`; mk_small_numeral k;
          `ibytes:byte list`;`xi:int128`;`ctr0:int128`;`k0:int128`;`k1:int128`;
          `k2:int128`;`k3:int128`;`k4:int128`;`k5:int128`;`k6:int128`;`k7:int128`;
          `k8:int128`;`k9:int128`;`k10:int128`;`k11:int128`;`k12:int128`;
          `k13:int128`;`k14:int128`;`h:int128`] WB_FRONT_BUF);;
(* intermediate assertion = WB_FRONT_BUF's postcond @ nblk:=k, normalized *)
let q_at k = rhs(concl(REWRITE_CONV[arith_16k k; arith_128k k]
  (vsubst [mk_small_numeral k,`nblk:num`] wb_front_postcond)));;
(* doubled frame for ENSURES_FRAME_SUBSUMED (F ,, F subsumes to F) *)
let fdbl_at k =
  let fs = subst [mk_small_numeral(16*k),`sss:num`]
    `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [memory :> bytes(out_p:int64, sss); memory :> bytes(xi_p:int64, 16);
                memory :> bytes(ivec_p:int64, 16); memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
     MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31]` in
  mk_binop `(,,):(armstate->armstate->bool)->(armstate->armstate->bool)->(armstate->armstate->bool)` fs fs;;

let mk_habbrev j =
  let hv = mk_var("h"^string_of_int j, `:int128`) in
  ABBREV_TAC (mk_eq(hv, mk_comb(`byteswap128:int128->int128`, hdot j))) THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`byteswap128:int128->int128`, hv), hdot j)) ASSUME_TAC THENL
  [EXPAND_TAC ("h"^string_of_int j) THEN REWRITE_TAC[BYTESWAP128_INVOLUTION]; ALL_TAC];;

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
    [MATCH_MP_TAC INPUT_BYTES_TO_BYTE128_LANES THEN
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
(* pc+3824 to the core exit pc+4556, is proved once per k as WB_TAIL_GEN2_k, *)
(* from a strictly weaker precondition than that of prove_band: q_at k       *)
(* without 5 cells that the tail does not read.  Both goals share the        *)
(* postcondition and the frame of mk_band_goal k, so the weak-precondition   *)
(* back-leg implies the full one by dropping conjuncts                       *)
(* (ENSURES_PRECONDITION_THM, no re-simulation), and WB_TAIL_GEN2_k serves   *)
(* both prove_band (below) and the nblk > 8 recomposition (WBN_PREP_TO_END,  *)
(* further below).                                                           *)
(*                                                                           *)
(* The 5 dropped cells (sp+72, xi_p, ivec_p, in_p block 0, X1) are never     *)
(* read by the tail code, [0xef0,0x11cc) and the exact-8 drain               *)
(* [0x11e4,0x1364).  X9 is not read either, but it is kept generically as    *)
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

(* The 4 seam memory cells the weak precondition drops, which the tail never
   reads (proving the back-legs without them checks this): [sp+72] is the
   zero the front stores next to the reduction constant at [sp+64]; xi_p and
   ivec_p are consumed only through Q19, Q16 (the tag) and Q0..Q7, Q30 (the
   counter); in_p block 0 arrives pre-loaded in Q9. *)
let wbn_tail_drop_lhs = [
  `read (memory :> bytes64 (word_add stackpointer (word 72))) (s:armstate)`;
  `read (memory :> bytes128 xi_p) (s:armstate)`;
  `read (memory :> bytes128 ivec_p) (s:armstate)`;
  `read (memory :> bytes128 in_p) (s:armstate)`];;

(* Replace the fixed per-band X9 count with a generic value.  The residual   *)
(* tail is shared by fixed bands (return_value = 16*r) and shifted           *)
(* whole-call tails (return_value = 16*nblk), and it does not write X9.      *)
let wbn_replace_x9 value pred =
  let sv, body = dest_abs pred in
  let x9lhs = subst [sv,`s:armstate`] `read X9 s` in
  let cs = conjuncts body in
  let cs' = map (fun c ->
    if is_eq c && lhs c = x9lhs then mk_eq(x9lhs,value) else c) cs in
  mk_abs(sv, end_itlist (curry mk_conj) cs');;

(* 5-cell drop: the 4 memory cells plus dead X1; X9 stays in the contract.   *)
let wbn_tail_drop_lhs5 = wbn_tail_drop_lhs @ [`read X1 (s:armstate)`];;
let wbn_weak_q_at5_return k return_value =
  let cs = conjuncts (snd(dest_abs (q_at k))) in
  let kept = filter (fun c -> not (is_eq c && mem (lhs c) wbn_tail_drop_lhs5)) cs in
  wbn_replace_x9 return_value
    (mk_abs(`s:armstate`, end_itlist (curry mk_conj) kept));;
let wbn_band_return k =
  subst [mk_small_numeral(16*k),`sss:num`] `word sss:int64`;;
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
(* ========================================================================= *)
(* 2. The symbolic counter layer.                                            *)
(*                                                                           *)
(* gcm_ctr_add w ivec adds w to the top 32-bit lane of ivec read             *)
(* byte-reversed, which gives the loop invariant a closed form of the        *)
(* counter at a symbolic block index (GCM_CTR_INC_ITER_AS_ADD):              *)
(*   gcm_ctr_inc_iter k x = gcm_ctr_add (word k) x.                          *)
(* The layer (gcm_ctr_add, GCM_CTR_ADD_LANES, GCM_CTR_INC_ITER_AS_ADD, and   *)
(* the SUBW_RAW lemmas and GCM_CTR_RAW_INCR of gcm_ctr_raw, which is defined *)
(* before wb_front_postcond) comes here, ahead of the nblk > 8 proof,        *)
(* because WB_IVEC_CLOSE_TAC below uses it for the counter write-back of the *)
(* band tails.                                                               *)
(*                                                                           *)
(* A direct BITBLAST of GCM_CTR_ADD_LANES does not scale: its BDD would      *)
(* contain the symbolic 32-bit addend.  The factoring below keeps every      *)
(* BITBLAST wiring-only, so that word_add never meets the BDD.               *)
(* ========================================================================= *)

let gcm_ctr_add = new_definition
 `gcm_ctr_add (w:32 word) (ivec:128 word) : 128 word =
   word_insert ivec (96,32)
     (word_bytereverse
        (word_add (word_bytereverse (word_subword ivec (96,32):(32)word)) w))`;;

let GCM_CTR_ADD_1 = prove
 (`gcm_ctr_add (word 1) = gcm_ctr_inc`,
  REWRITE_TAC[FUN_EQ_THM; gcm_ctr_add; gcm_ctr_inc]);;

(* wiring-only: byte decomposition of the byte-reversed top lane *)
let BREV_TOP_LANE = prove
 (`!ctr0:int128.
     word_bytereverse (word_subword ctr0 (96,32):32 word) =
     word_join
      (word_join (word_subword ctr0 (96,8):8 word) (word_subword ctr0 (104,8):8 word):16 word)
      (word_join (word_subword ctr0 (112,8):8 word) (word_subword ctr0 (120,8):8 word):16 word)`,
  GEN_TAC THEN BITBLAST_TAC);;

(* wiring-only: insert of brev s as the byte-join tower; s stays free, so the
   abstract add never enters the BDD *)
let INSERT_BREV_WIRING = prove
 (`!(ctr0:int128) (s:32 word).
     word_insert ctr0 (96,32) (word_bytereverse s) : 128 word =
     word_join
      (word_join
       (word_join
        (word_join (word_subword s (0,8):8 word) (word_subword s (8,8):8 word):16 word)
        (word_join (word_subword s (16,8):8 word) (word_subword s (24,8):8 word):16 word)
        :32 word)
       (word_join
        (word_join (word_subword ctr0 (88,8):8 word) (word_subword ctr0 (80,8):8 word):16 word)
        (word_join (word_subword ctr0 (72,8):8 word) (word_subword ctr0 (64,8):8 word):16 word)
        :32 word) :64 word)
      (word_join
       (word_join
        (word_join (word_subword ctr0 (56,8):8 word) (word_subword ctr0 (48,8):8 word):16 word)
        (word_join (word_subword ctr0 (40,8):8 word) (word_subword ctr0 (32,8):8 word):16 word)
        :32 word)
       (word_join
        (word_join (word_subword ctr0 (24,8):8 word) (word_subword ctr0 (16,8):8 word):16 word)
        (word_join (word_subword ctr0 (8,8):8 word) (word_subword ctr0 (0,8):8 word):16 word)
        :32 word) :64 word)`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

(* the generic-w lanes lemma: RHS built programmatically from
   GCM_CTR_INC_LANES with `w` for `word 1` (exactly the Q-lane shape the
   front simulation produces); proof is pure rewriting *)
let GCM_CTR_ADD_LANES =
  let lanes_w = subst [`w:32 word`,`word 1:32 word`]
    (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES)))) in
  let gl = list_mk_forall([`w:32 word`;`ctr0:int128`],
    mk_eq(list_mk_comb(`gcm_ctr_add`,[`w:32 word`;`ctr0:int128`]), lanes_w)) in
  prove(gl,
    REPEAT GEN_TAC THEN
    REWRITE_TAC[gcm_ctr_add; BREV_TOP_LANE; INSERT_BREV_WIRING]);;

(* algebra of the symbolic add *)
let SUBWORD_INSERT_TOP = prove
 (`!(x:int128) (v:32 word). word_subword (word_insert x (96,32) v : int128) (96,32) = v`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

let INSERT_INSERT_TOP = prove
 (`!(x:int128) (u:32 word) (v:32 word).
     word_insert (word_insert x (96,32) (u:32 word) : int128) (96,32) (v:32 word) : int128 =
     word_insert x (96,32) v`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

let BREV_BREV_32 = prove
 (`!s:32 word. word_bytereverse (word_bytereverse s) = s`,
  GEN_TAC THEN BITBLAST_TAC);;

let INSERT_SELF_TOP = prove
 (`!x:int128. word_insert x (96,32) (word_subword x (96,32):32 word) : int128 = x`,
  GEN_TAC THEN BITBLAST_TAC);;

let GCM_CTR_ADD_COMPOSE = prove
 (`!(u:32 word) (v:32 word) (x:int128).
     gcm_ctr_add v (gcm_ctr_add u x) = gcm_ctr_add (word_add u v) x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gcm_ctr_add] THEN
  REWRITE_TAC[SUBWORD_INSERT_TOP; INSERT_INSERT_TOP; BREV_BREV_32] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

let GCM_CTR_ADD_0 = prove
 (`!x:int128. gcm_ctr_add (word 0) x = x`,
  GEN_TAC THEN REWRITE_TAC[gcm_ctr_add; WORD_ADD_0; BREV_BREV_32; INSERT_SELF_TOP]);;

(* the closed form the ENSURES_WHILE invariant needs: counter at symbolic
   block index k *)
let GCM_CTR_INC_ITER_AS_ADD = prove
 (`!k x:int128. gcm_ctr_inc_iter k x = gcm_ctr_add (word k) x`,
  INDUCT_TAC THEN GEN_TAC THENL
   [REWRITE_TAC[gcm_ctr_inc_iter; GCM_CTR_ADD_0];
    ASM_REWRITE_TAC[gcm_ctr_inc_iter] THEN
    REWRITE_TAC[GSYM GCM_CTR_ADD_1; GCM_CTR_ADD_COMPOSE] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[ADD1; GSYM WORD_ADD] THEN
    CONV_TAC WORD_RULE]);;

(* The 4 lane-extraction lemmas of gcm_ctr_raw, which prove GCM_CTR_RAW_INCR
   without a WORD_BLAST over the symbolic w (which does not scale, as for
   GCM_CTR_ADD_LANES above).  Each is WORD_SIMPLE_SUBWORD_CONV, which extracts
   the lane, then WORD_BLAST: w only appears added to the top lane, so the
   addend never enters the BDD. *)
let SUBW_RAW_96 = prove
 (`word_subword (gcm_ctr_raw w ctr0) (96,32):32 word =
   word_add (word_join (word_join (word_subword ctr0 (96,8):8 word) (word_subword ctr0 (104,8):8 word):16 word)
     (word_join (word_subword ctr0 (112,8):8 word) (word_subword ctr0 (120,8):8 word):16 word):32 word) w`,
  REWRITE_TAC[gcm_ctr_raw_def] THEN CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN CONV_TAC WORD_BLAST);;
let SUBW_RAW_64 = prove
 (`word_subword (gcm_ctr_raw w ctr0) (64,32):32 word =
   word_join (word_join (word_subword ctr0 (64,8):8 word) (word_subword ctr0 (72,8):8 word):16 word)
     (word_join (word_subword ctr0 (80,8):8 word) (word_subword ctr0 (88,8):8 word):16 word):32 word`,
  REWRITE_TAC[gcm_ctr_raw_def] THEN CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN CONV_TAC WORD_BLAST);;
let SUBW_RAW_32 = prove
 (`word_subword (gcm_ctr_raw w ctr0) (32,32):32 word =
   word_join (word_join (word_subword ctr0 (32,8):8 word) (word_subword ctr0 (40,8):8 word):16 word)
     (word_join (word_subword ctr0 (48,8):8 word) (word_subword ctr0 (56,8):8 word):16 word):32 word`,
  REWRITE_TAC[gcm_ctr_raw_def] THEN CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN CONV_TAC WORD_BLAST);;
let SUBW_RAW_0 = prove
 (`word_subword (gcm_ctr_raw w ctr0) (0,32):32 word =
   word_join (word_join (word_subword ctr0 (0,8):8 word) (word_subword ctr0 (8,8):8 word):16 word)
     (word_join (word_subword ctr0 (16,8):8 word) (word_subword ctr0 (24,8):8 word):16 word):32 word`,
  REWRITE_TAC[gcm_ctr_raw_def] THEN CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN CONV_TAC WORD_BLAST);;

(* The increment add v30.4s,v30.4s,v31.4s (v31 = word 2^96) is a lane-wise
   32-bit add: the model emits it as a word_join of
   word_add (word_subword v30 lane) (word c), with c = 1 on the top lane and
   0 on the others.  It advances the raw counter by 1. *)
let GCM_CTR_RAW_INCR = prove
 (`word_join
    (word_join
     (word_add (word_subword (gcm_ctr_raw w ctr0) (96,32):32 word) (word 1))
     (word_add (word_subword (gcm_ctr_raw w ctr0) (64,32):32 word) (word 0)):64 word)
    (word_join
     (word_add (word_subword (gcm_ctr_raw w ctr0) (32,32):32 word) (word 0))
     (word_add (word_subword (gcm_ctr_raw w ctr0) (0,32):32 word) (word 0)):64 word):int128 =
    gcm_ctr_raw (word_add w (word 1)) ctr0`,
  REWRITE_TAC[SUBW_RAW_96; SUBW_RAW_64; SUBW_RAW_32; SUBW_RAW_0; WORD_ADD_0] THEN
  GEN_REWRITE_TAC RAND_CONV [gcm_ctr_raw_def] THEN
  REWRITE_TAC[WORD_RULE
    `!(x:32 word) w. word_add (word_add x w) (word 1) = word_add x (word_add w (word 1))`]);;

(* ------------------------------------------------------------------------- *)
(* The band-tail ivec write-back closer.                                     *)
(*                                                                           *)
(* Each band r stores rev32(v30) to [ivec_p] at the end of its tail.  The    *)
(* counter register comes in from the seam as                                *)
(*   Q30 = gcm_ctr_raw (word 8) ctr0,                                        *)
(* and the cascade decrements it 8 - r times by sub v30 (the exact-8 drain,  *)
(* r = 8, not at all), so the stored value is                                *)
(*   rev32 (gcm_ctr_raw (word r) ctr0) = gcm_ctr_add (word r) ctr0           *)
(*                                     = gcm_ctr_inc_iter r ctr0.            *)
(* The close runs entirely in 32-bit-lane algebra (SUBW_RAW_* pin the sub    *)
(* cascade to the top lane, GCM_CTR_ADD_LANES gives the reversed target), so *)
(* that no 128-bit blast meets the symbolic counter.                         *)
(* ------------------------------------------------------------------------- *)
let sub_chain c n =
  let rec build acc k = if k=0 then acc
    else build (mk_comb(mk_comb(`word_sub:32 word->32 word->32 word`,acc),
                        mk_comb(`word:num->32 word`,mk_small_numeral c))) (k-1) in
  let lh = build `x:32 word` n in
  WORD_RULE(mk_eq(lh, if c=0 then `x:32 word`
                       else mk_comb(mk_comb(`word_sub:32 word->32 word->32 word`,`x:32 word`),
                                    mk_comb(`word:num->32 word`,mk_small_numeral n))));;
let SUBW_NORM r = WORD_RULE(subst[mk_small_numeral(8-r),`d:num`; mk_small_numeral r,`rr:num`]
  `word_sub (word_add (x:32 word) (word 8)) (word d) = word_add x (word rr)`);;
let WB_IVEC_CLOSE_TAC r =
  REWRITE_TAC[GCM_CTR_INC_ITER_AS_ADD] THEN
  REWRITE_TAC[sub_chain 1 (8-r); sub_chain 0 (8-r)] THEN
  REWRITE_TAC[gcm_ctr_raw_def; SUBW_RAW_96; SUBW_RAW_64; SUBW_RAW_32; SUBW_RAW_0] THEN
  REWRITE_TAC[SUBW_NORM r; WORD_SUB_0] THEN
  GEN_REWRITE_TAC RAND_CONV [GCM_CTR_ADD_LANES] THEN
  W(fun (_,gw) ->
     let atom = find_term (fun t -> match t with
       | Comb(Comb(Const("word_add",_),_),Comb(Const("word",_),_)) -> true | _ -> false) gw in
     SPEC_TAC(atom, `aa:32 word`)) THEN
  GEN_TAC THEN CONV_TAC WORD_BLAST;;

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

(* ========================================================================= *)
(* The small-message path, nblk <= 4.  The b.le at 0x38 (front step 8)       *)
(* branches to L256_dec_small (0x1364), which loads the counter, the tag and *)
(* the 15 round keys and dispatches on x9 (through L256_dec_small_ge3 for    *)
(* nblk >= 3) to L256_dec_small_seed_k.  small_seed_k seeds the GHASH        *)
(* accumulator with Xi' * H^k and enters the chain small_blk_k, ..,          *)
(* small_blk_1 at small_blk_k: each decrypts one block and folds its         *)
(* ciphertext into the accumulator with the matching power of H;             *)
(* small_blk_1 also reduces, stores the tag, the counter and the last        *)
(* plaintext block, and L256_dec_small_done branches to                      *)
(* L256_dec_frame_restore (0x11cc, pc+4556), the core exit.                  *)
(*                                                                           *)
(* WB_FUSED_kBLOCK (k = 1..4) proves each path from the core entry pc+0x1c,  *)
(* and mk_band_from_fused restates it as the band goal mk_band_goal k by     *)
(* ENSURES_PRECONDITION_THM, without re-simulation (prove_band needs         *)
(* 5 <= nblk).  The four proofs share the tactics that follow: the KEEPGHALL *)
(* discard and stepper, which keep the GHASH accumulators across a window,   *)
(* JOIN_IS_CTR0, INLINE_SELFCONTAINED and DEC_BRIDGE_ROUTEB_TAC, the GHASH   *)
(* bridge for k >= 2; the k = 1 bridge has its own lemmas and closer.        *)
(* ========================================================================= *)

(* KEEPGHALL discard: drop every fact that mentions an older state, except
   the facts about Q16-Q26 and Q30 and the key-table reads, so that the GHASH
   accumulators and their operands survive. *)
let DISCARD_OLDSTATE_KEEPGHALL_TAC s =
  let v = mk_var(s,`:armstate`) in
  let rec unbound_statevars_of_read bound tm = match tm with
      Comb(Comb(Const("read",_),_),st) -> if mem st bound then [] else [st]
    | Comb(a,b) -> union (unbound_statevars_of_read bound a) (unbound_statevars_of_read bound b)
    | Abs(vv,t) -> unbound_statevars_of_read (vv::bound) t | _ -> [] in
  let rec mentions_htbl t = match t with
      Var("htbl_p",_) -> true
    | Comb(a,b) -> mentions_htbl a || mentions_htbl b | Abs(_,t2) -> mentions_htbl t2 | _ -> false in
  let rec mentions_ghreg t = match t with
      Comb(Comb(Const("read",_),cmp),_) ->
        (match cmp with Const(n,_) -> n="Q16"||n="Q17"||n="Q18"||n="Q19"||n="Q20"||n="Q21"||n="Q22"||n="Q23"||n="Q24"||n="Q25"||n="Q26"||n="Q30" | _ -> false)
    | Comb(a,b) -> mentions_ghreg a || mentions_ghreg b | Abs(_,t2) -> mentions_ghreg t2 | _ -> false in
  DISCARD_ASSUMPTIONS_TAC(fun thm ->
    if mentions_ghreg (concl thm) then false else
    if (match concl thm with
        | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),cmp),_)),_) -> mentions_htbl cmp
        | _ -> false) then false else
    let us = unbound_statevars_of_read [] (concl thm) in
    if us = [] || us = [v] then false else if not(mem v us) then true else true);;

(* The per-step normalizer of the small path, Q-scoped and fixpoint-memoized.
   GCM_SIMD_SIMPLIFY_CORE_QSCOPED_TAC applies the three rewrite passes of
   GCM_SIMD_SIMPLIFY_CORE_TAC to the `read Qn s = ...` assumptions only, and
   skips those whose conclusion gcm_simd_fixpt_tbl records as already at a
   fixpoint.  In the KEEPGHALL windows the discard keeps the whole multi-block
   GHASH accumulator history, so the assumption list grows large, and most of
   it (memory reads, nonoverlapping facts, flags) is never rewritten by the
   SIMD rules.  The passes act on an assumption through its conclusion alone,
   so skipping a recorded fixpoint gives the same result as applying them.
   CLEAR_KEEPGHALL_MEMO_TAC empties the table at the start of each
   WB_FUSED_kBLOCK proof, so that each proof is hermetic. *)
let gcm_simd_fixpt_tbl : (term,unit) Hashtbl.t = Hashtbl.create 8192;;
let CLEAR_KEEPGHALL_MEMO_TAC : tactic =
  fun (asl,w) -> Hashtbl.clear gcm_simd_fixpt_tbl; ALL_TAC (asl,w);;
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

(* Block 0's AES input is rev32 of rev32 of the loaded counter block ctr0,
   which the simulation leaves as the join of the sixteen bytes of ctr0. *)
let JOIN_IS_CTR0 = prove(
 `word_join
    (word_join
     (word_join
      (word_join (word_subword (ctr0:int128) (120,8):8 word) (word_subword ctr0 (112,8):8 word):16 word)
      (word_join (word_subword ctr0 (104,8):8 word) (word_subword ctr0 (96,8):8 word):16 word):32 word)
     (word_join
      (word_join (word_subword ctr0 (88,8):8 word) (word_subword ctr0 (80,8):8 word):16 word)
      (word_join (word_subword ctr0 (72,8):8 word) (word_subword ctr0 (64,8):8 word):16 word):32 word):64 word)
    (word_join
     (word_join
      (word_join (word_subword ctr0 (56,8):8 word) (word_subword ctr0 (48,8):8 word):16 word)
      (word_join (word_subword ctr0 (40,8):8 word) (word_subword ctr0 (32,8):8 word):16 word):32 word)
     (word_join
      (word_join (word_subword ctr0 (24,8):8 word) (word_subword ctr0 (16,8):8 word):16 word)
      (word_join (word_subword ctr0 (8,8):8 word) (word_subword ctr0 (0,8):8 word):16 word):32 word):64 word):int128
  = ctr0`,
  CONV_TAC WORD_BLAST);;

(* INLINE_SELFCONTAINED reg st npass: rewrite `read reg st = ...` with the
   facts about the other states until its right side mentions no other state
   (at most npass rounds), so that the older states can be discarded. *)
let INLINE_SELFCONTAINED reg st npass : tactic = fun (asl,w) ->
  let lhs_t = parse_term (Printf.sprintf "read %s %s" reg st) in
  let rec nonSt tm = match tm with
      Comb(Comb(Const("read",_),_),stv) ->
        (match stv with Var(n,_) when n<>st -> [stv] | _ -> [])
    | Comb(a,b) -> union (nonSt a) (nonSt b) | Abs(_,t) -> nonSt t | _ -> [] in
  let target_rhs aslx =
    try rhs(concl(snd(List.find (fun (_,th) -> try lhs(concl th)=lhs_t with _->false) aslx)))
    with Not_found -> `T` in
  let rec go n (asl,w) =
    if n <= 0 then ALL_TAC (asl,w)
    else if nonSt (target_rhs asl) = [] then ALL_TAC (asl,w)
    else
      let picks = mapfilter (fun (_,th) ->
        match concl th with
        | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),stv)),_)
            when (match stv with Var(nm,_)->nm<>st|_->false) -> th
        | _ -> fail()) asl in
      (RULE_ASSUM_TAC(fun th ->
         if (try lhs(concl th) = lhs_t with _ -> false)
         then REWRITE_RULE picks th else th) THEN go (n-1)) (asl,w) in
  go npass (asl,w);;

(* DEC_BRIDGE_ROUTEB_TAC: the GHASH bridge close for k >= 2.  The bridges
   BRIDGE_CLOSE_{2,3,4}_CPH*_TAC below are thin wrappers of it: they share the
   prelude and the finisher and differ only in the spec equation spec_eq and
   in three identities between Karatsuba products that MERGE_2BLK_TAC does
   not pair.  The machine multiplies the seed and block 0 by H^k separately,
   the spec multiplies their XOR once, so each identity says that a product
   whose operand is an XOR is the XOR of the products of the two parts:
   bridge_qq_land distributes the product over the XOR (CONJUNCT1
   WORD_PMUL_XOR); bridge_qq_mid, for the middle product, whose operands are
   nested subword/join terms, folds the two parts and compares the operands
   (PMUL_CONG_128, WORD_BLAST).  The caller passes the bridge state sN,
   spec_eq (from its spec_to_byteform lemma, GMULTk_FULL_CORRECT_BA at its
   dec_bridge_specl list and the H-power facts) and the three
   (product, part, part) name triples. *)
let bridge_qq_land (a,b,c) : tactic =
  SUBGOAL_THEN (parse_term (Printf.sprintf "(%s:int128) = word_xor %s %s" a b c))
    (fun th -> REWRITE_TAC[th]) THENL
   [MAP_EVERY EXPAND_TAC [a;b;c] THEN
    GEN_REWRITE_TAC LAND_CONV [CONJUNCT1 WORD_PMUL_XOR] THEN
    REWRITE_TAC[WORD_XOR_ACI]; ALL_TAC];;

let bridge_qq_mid (a,b,c) : tactic =
  SUBGOAL_THEN (parse_term (Printf.sprintf "(%s:int128) = word_xor %s %s" a b c))
    (fun th -> REWRITE_TAC[th]) THENL
   [MAP_EVERY EXPAND_TAC [a;b;c] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM (CONJUNCT1 WORD_PMUL_XOR)] THEN
    MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC];;

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
let FOLD_MID2 = prove(
  `word_xor
     (word_pmul
       (word_xor
         (word_subword
           (word_subword
             (word_join (word_reversefields 8 (cph:int128)) (word_reversefields 8 cph):256 word) (64,128):128 word)
            (0,64):64 word)
         (word_reversefields 8 (word_subword cph (64,64):64 word)))
       (word_xor (word_subword (h:int128) (0,64):64 word) (word_subword h (64,64):64 word)))
     (word_pmul
       (word_xor
         (word_subword
           (word_subword
             (word_join
               (word_join (word_reversefields 8 (word_subword (xi:int128) (0,64):64 word))
                          (word_reversefields 8 (word_subword xi (64,64):64 word)):128 word)
               (word_join (word_reversefields 8 (word_subword xi (0,64):64 word))
                          (word_reversefields 8 (word_subword xi (64,64):64 word)):128 word):256 word)
             (64,128):128 word)
            (0,64):64 word)
         (word_reversefields 8 (word_subword xi (64,64):64 word)))
       (word_xor (word_subword h (0,64):64 word) (word_subword h (64,64):64 word))) : int128
   = word_pmul (word_xor (word_subword h (64,64):64 word) (word_subword h (0,64):64 word))
       (word_xor
         (word_xor (word_reversefields 8 (word_subword xi (64,64):64 word))
                   (word_reversefields 8 (word_subword cph (64,64):64 word)))
         (word_xor (word_reversefields 8 (word_subword xi (0,64):64 word))
                   (word_reversefields 8 (word_subword cph (0,64):64 word))))`,
  REWRITE_TAC[JOINMID; JOIN_SUBWORD_RULES; WORD_SUBWORD_SUBWORD; RF8_SUBWORD] THEN
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
   core exit pc+4556.  s1-s8 the front and the dispatch (the b.le at s8 is
   taken), s9-s29 L256_dec_small (the counter, tag and round-key loads and
   the x9 compares), s30-s37 L256_dec_small_seed_1 (the seed Xi' * H),
   s38-s96 L256_dec_small_blk_1 (the AES-256 tower, the reduced GHASH at
   s84, ext and rev64 at s87 and s88, the tag store at s91, the counter store
   at s94, the plaintext eor3 at s95 and its store at s96), s97 the b at
   L256_dec_small_done.  The KEEPGHALL stepper runs from the first seed
   product (s34) to the reduce, where BRIDGE_CLOSE_FULL_TAC proves Q19 to be
   the one-block GHASH (gval). *)
let WB_FUSED_1BLOCK = prove(
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    cph xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk.
    aligned 16 stackpointer /\
    nonoverlapping (word pc, 5956) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, 5956) (out_p:int64, 16) /\
    nonoverlapping (word pc, 5956) (xi_p:int64, 16) /\
    nonoverlapping (word pc, 5956) (ivec_p:int64, 16) /\
    nonoverlapping (out_p, 16) (xi_p, 16) /\
    nonoverlapping (out_p, 16) (ivec_p, 16) /\
    nonoverlapping (xi_p, 16) (ivec_p, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 16) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 240) /\
    nonoverlapping (ivec_p, 16) (htbl_p:int64, 192) /\
    nonoverlapping (in_p, 16) (stackpointer, 80) /\
    nonoverlapping (key_p, 240) (stackpointer, 80) /\
    nonoverlapping (htbl_p, 192) (stackpointer, 80) /\
    nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
    nonoverlapping (xi_p, 16) (in_p, 16) /\
    nonoverlapping (xi_p, 16) (key_p, 240) /\
    nonoverlapping (xi_p, 16) (htbl_p, 192) /\
    nonoverlapping (xi_p, 16) (stackpointer, 80) /\
    nonoverlapping (out_p, 16) (in_p, 16) /\
    nonoverlapping (out_p, 16) (key_p, 240) /\
    nonoverlapping (out_p, 16) (htbl_p, 192) /\
    nonoverlapping (out_p, 16) (stackpointer, 80) /\
    word_subword hk (0,64) :64 word =
      word_xor (word_subword h (0,64):64 word) (word_subword h (64,64):64 word)
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
          read PC s = word (pc + 0x1c) /\ read SP s = stackpointer /\
          C_ARGUMENTS [in_p; word 128; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
          read (memory :> bytes128 in_p) s = cph /\
          read (memory :> bytes128 xi_p) s = xi /\
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
          read (memory :> bytes128 htbl_p) s = h /\
          read (memory :> bytes128 (word_add htbl_p (word 16))) s = hk)
     (\s. read PC s = word (pc + 0x11cc) /\
          read X9 s = word 16 /\
          read (memory :> bytes128 out_p) s =
          word_xor cph (aes256_encrypt ctr0
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 xi_p) s =
          word_bytereverse
            (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
              [word_bytereverse cph]) /\
          read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 1 ctr0)
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(out_p, 16); memory :> bytes(xi_p, 16);
                 memory :> bytes(ivec_p, 16);
                 memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  CLEAR_KEEPGHALL_MEMO_TAC THEN  (* empty the normalizer fixpoint table *)
  FIRST_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 (word_add htbl_p (word 16))) s0`
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

(* ---- nblk = 2 ---- *)

let spec_to_byteform_2 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1] =
       polyval_reduce_prop3
        (word_xor
          (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h2))
          (word_pmul (word_bytereverse cph1) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`] GHASH_POLYVAL_ACC_2)] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

let dec_bridge_specl_2_cph1 =
  [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h2:int128`;
   `word_bytereverse cph1:int128`; `byteswap128 h:int128`];;

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
   (1) the hk read (htbl_p+16) is split into its 64-bit halves, and the
       address of the high half, htbl_p+16+8, is normalized to htbl_p+24, the
       address of the ldr d25,[x6,#24] that loads the Karatsuba mid of H^2;
       otherwise that load is not resolved and the discard drops the Q18
       accumulator that depends on it (nblk = 1 has no such load);
   (2) Q17-Q19 are made self-contained at the block-0 store s81
       (INLINE_SELFCONTAINED) before the discard, so that the accumulator
       chain of block 0 survives it.
   BRIDGE_CLOSE_2_CPH1_TAC closes Q19 at the reduce s128. *)
let WB_FUSED_2BLOCK = prove(
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    cph0 cph1 xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk h2.
    aligned 16 stackpointer /\
    nonoverlapping (word pc, 5956) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, 5956) (out_p:int64, 32) /\
    nonoverlapping (word pc, 5956) (xi_p:int64, 16) /\
    nonoverlapping (word pc, 5956) (ivec_p:int64, 16) /\
    nonoverlapping (out_p, 32) (xi_p, 16) /\
    nonoverlapping (out_p, 32) (ivec_p, 16) /\
    nonoverlapping (xi_p, 16) (ivec_p, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 32) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 240) /\
    nonoverlapping (ivec_p, 16) (htbl_p:int64, 192) /\
    nonoverlapping (in_p, 32) (stackpointer, 80) /\
    nonoverlapping (key_p, 240) (stackpointer, 80) /\
    nonoverlapping (htbl_p, 192) (stackpointer, 80) /\
    nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
    nonoverlapping (xi_p, 16) (in_p, 32) /\
    nonoverlapping (xi_p, 16) (key_p, 240) /\
    nonoverlapping (xi_p, 16) (htbl_p, 192) /\
    nonoverlapping (xi_p, 16) (stackpointer, 80) /\
    nonoverlapping (out_p, 32) (in_p, 32) /\
    nonoverlapping (out_p, 32) (key_p, 240) /\
    nonoverlapping (out_p, 32) (htbl_p, 192) /\
    nonoverlapping (out_p, 32) (stackpointer, 80) /\
    word_subword hk (0,64) :64 word =
      word_xor (word_subword h (0,64):64 word) (word_subword h (64,64):64 word) /\
    word_subword hk (64,64) :64 word =
      word_xor (word_subword h2 (0,64):64 word) (word_subword h2 (64,64):64 word) /\
    byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h)
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
          read PC s = word (pc + 0x1c) /\ read SP s = stackpointer /\
          C_ARGUMENTS [in_p; word 256; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
          read (memory :> bytes128 in_p) s = cph0 /\
          read (memory :> bytes128 (word_add in_p (word 16))) s = cph1 /\
          read (memory :> bytes128 xi_p) s = xi /\
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
          read (memory :> bytes128 htbl_p) s = h /\
          read (memory :> bytes128 (word_add htbl_p (word 16))) s = hk /\
          read (memory :> bytes128 (word_add htbl_p (word 32))) s = h2)
     (\s. read PC s = word (pc + 0x11cc) /\
          read X9 s = word 32 /\
          read (memory :> bytes128 out_p) s =
          word_xor cph0 (aes256_encrypt ctr0
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 (word_add out_p (word 16))) s =
          word_xor cph1 (aes256_encrypt (gcm_ctr_inc ctr0)
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 xi_p) s =
          word_bytereverse
            (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
              [word_bytereverse cph0; word_bytereverse cph1]) /\
          read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 2 ctr0)
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(out_p, 32); memory :> bytes(xi_p, 16);
                 memory :> bytes(ivec_p, 16);
                 memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  CLEAR_KEEPGHALL_MEMO_TAC THEN  (* empty the normalizer fixpoint table *)
  FIRST_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 (word_add htbl_p (word 16))) s0`
        with _ -> false)
    then (MP_TAC th THEN PURE_ONCE_REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] THEN
          STRIP_TAC)
    else NO_TAC) THEN
  (* detail (1): htbl_p+16+8 = htbl_p+24 *)
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_add (htbl_p:int64) (word 16)) (word 8) = word_add htbl_p (word 24)`]) THEN
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
   MAYCHANGE [memory :> bytes128 (word_add out_p (word 16))] ,, MAYCHANGE [memory :> bytes128 xi_p] ,,
   MAYCHANGE [memory :> bytes128 ivec_p] ,,
   MAYCHANGE [memory :> bytes128 (word_add out_p (word 32))]
   :armstate->armstate->bool) subsumed
  (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
   MAYCHANGE [memory :> bytes(out_p:int64, 48); memory :> bytes(xi_p:int64,16);
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

(* The GMULT3_FULL_CORRECT_BA operands for nblk = 3: block 0 with the tag
   folded in times H^3, block 1 times H^2, block 2 times H (byte-reversed
   blocks, byteswapped key powers). *)
let dec_bridge_specl_3_cph2 =
  [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h3:int128`;
   `word_bytereverse cph1:int128`; `byteswap128 h2:int128`;
   `word_bytereverse cph2:int128`; `byteswap128 h:int128`];;

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
   The table reads hk (htbl_p+16) and h3k (htbl_p+64) are split into their
   64-bit halves, which hold the Karatsuba mids the blocks load: of H at +16,
   of H^2 at +24, of H^3 at +64.  The simulation runs in windows that end at
   the block stores s80 and s123, where the block just stored is captured,
   and at the reduce s170; at each cut the accumulators are made
   self-contained, so that the older states can be discarded.
   BRIDGE_CLOSE_3_CPH2_TAC closes Q19 at s170, and the frame closes by
   WB3_FRAME_IMP. *)
let WB_FUSED_3BLOCK = prove(
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    cph0 cph1 cph2 xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk h2 h3 h3k.
    aligned 16 stackpointer /\
    nonoverlapping (word pc, 5956) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, 5956) (out_p:int64, 48) /\
    nonoverlapping (word pc, 5956) (xi_p:int64, 16) /\
    nonoverlapping (word pc, 5956) (ivec_p:int64, 16) /\
    nonoverlapping (out_p, 48) (xi_p, 16) /\
    nonoverlapping (out_p, 48) (ivec_p, 16) /\
    nonoverlapping (xi_p, 16) (ivec_p, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 48) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 240) /\
    nonoverlapping (ivec_p, 16) (htbl_p:int64, 192) /\
    nonoverlapping (in_p, 48) (stackpointer, 80) /\
    nonoverlapping (key_p, 240) (stackpointer, 80) /\
    nonoverlapping (htbl_p, 192) (stackpointer, 80) /\
    nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
    nonoverlapping (xi_p, 16) (in_p, 48) /\
    nonoverlapping (xi_p, 16) (key_p, 240) /\
    nonoverlapping (xi_p, 16) (htbl_p, 192) /\
    nonoverlapping (xi_p, 16) (stackpointer, 80) /\
    nonoverlapping (out_p, 48) (in_p, 48) /\
    nonoverlapping (out_p, 48) (key_p, 240) /\
    nonoverlapping (out_p, 48) (htbl_p, 192) /\
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
          C_ARGUMENTS [in_p; word 384; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
          read (memory :> bytes128 in_p) s = cph0 /\
          read (memory :> bytes128 (word_add in_p (word 16))) s = cph1 /\
          read (memory :> bytes128 (word_add in_p (word 32))) s = cph2 /\
          read (memory :> bytes128 xi_p) s = xi /\
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
          read (memory :> bytes128 htbl_p) s = h /\
          read (memory :> bytes128 (word_add htbl_p (word 16))) s = hk /\
          read (memory :> bytes128 (word_add htbl_p (word 32))) s = h2 /\
          read (memory :> bytes128 (word_add htbl_p (word 48))) s = h3 /\
          read (memory :> bytes128 (word_add htbl_p (word 64))) s = h3k)
     (\s. read PC s = word (pc + 0x11cc) /\
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
          read (memory :> bytes128 xi_p) s =
          word_bytereverse
            (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
              [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2]) /\
          read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 3 ctr0)
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(out_p, 48); memory :> bytes(xi_p, 16);
                 memory :> bytes(ivec_p, 16);
                 memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  CLEAR_KEEPGHALL_MEMO_TAC THEN  (* empty the normalizer fixpoint table *)
  (* split hk at htbl_p+16: the Karatsuba mids of H (low) and H^2 (high) *)
  FIRST_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 (word_add htbl_p (word 16))) s0`
        with _ -> false)
    then (MP_TAC th THEN PURE_ONCE_REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] THEN
          STRIP_TAC)
    else NO_TAC) THEN
  (* split h3k at htbl_p+64: the Karatsuba mid of H^3 (low) *)
  FIRST_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 (word_add htbl_p (word 64))) s0`
        with _ -> false)
    then (MP_TAC th THEN PURE_ONCE_REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] THEN
          STRIP_TAC)
    else NO_TAC) THEN
  (* htbl_p+16+8 = htbl_p+24, the address of the ldr d25,[x6,#24] *)
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_add (htbl_p:int64) (word 16)) (word 8) = word_add htbl_p (word 24)`]) THEN
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
   MAYCHANGE [memory :> bytes128 xi_p] ,,
   MAYCHANGE [memory :> bytes128 ivec_p] ,,
   MAYCHANGE [memory :> bytes128 (word_add out_p (word 48))]
   :armstate->armstate->bool) subsumed
  (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
   MAYCHANGE [memory :> bytes(out_p:int64, 64); memory :> bytes(xi_p:int64,16);
              memory :> bytes(ivec_p:int64,16);
              memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
   MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
              Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC);;

let WB4_FRAME_IMP =
  SPECL [`s0:armstate`; `s227:armstate`] (REWRITE_RULE[subsumed] WB4_FRAME_SUBSUMED);;

let dec_bridge_specl_4_cph3 =
  [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h4:int128`;
   `word_bytereverse cph1:int128`; `byteswap128 h3:int128`;
   `word_bytereverse cph2:int128`; `byteswap128 h2:int128`;
   `word_bytereverse cph3:int128`; `byteswap128 h:int128`];;

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
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    cph0 cph1 cph2 cph3 xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk h2 h3 h3k h4.
    aligned 16 stackpointer /\
    nonoverlapping (word pc, 5956) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, 5956) (out_p:int64, 64) /\
    nonoverlapping (word pc, 5956) (xi_p:int64, 16) /\
    nonoverlapping (word pc, 5956) (ivec_p:int64, 16) /\
    nonoverlapping (out_p, 64) (xi_p, 16) /\
    nonoverlapping (out_p, 64) (ivec_p, 16) /\
    nonoverlapping (xi_p, 16) (ivec_p, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 64) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 240) /\
    nonoverlapping (ivec_p, 16) (htbl_p:int64, 192) /\
    nonoverlapping (in_p, 64) (stackpointer, 80) /\
    nonoverlapping (key_p, 240) (stackpointer, 80) /\
    nonoverlapping (htbl_p, 192) (stackpointer, 80) /\
    nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
    nonoverlapping (xi_p, 16) (in_p, 64) /\
    nonoverlapping (xi_p, 16) (key_p, 240) /\
    nonoverlapping (xi_p, 16) (htbl_p, 192) /\
    nonoverlapping (xi_p, 16) (stackpointer, 80) /\
    nonoverlapping (out_p, 64) (in_p, 64) /\
    nonoverlapping (out_p, 64) (key_p, 240) /\
    nonoverlapping (out_p, 64) (htbl_p, 192) /\
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
          C_ARGUMENTS [in_p; word 512; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
          read (memory :> bytes128 in_p) s = cph0 /\
          read (memory :> bytes128 (word_add in_p (word 16))) s = cph1 /\
          read (memory :> bytes128 (word_add in_p (word 32))) s = cph2 /\
          read (memory :> bytes128 (word_add in_p (word 48))) s = cph3 /\
          read (memory :> bytes128 xi_p) s = xi /\
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
          read (memory :> bytes128 htbl_p) s = h /\
          read (memory :> bytes128 (word_add htbl_p (word 16))) s = hk /\
          read (memory :> bytes128 (word_add htbl_p (word 32))) s = h2 /\
          read (memory :> bytes128 (word_add htbl_p (word 48))) s = h3 /\
          read (memory :> bytes128 (word_add htbl_p (word 64))) s = h3k /\
          read (memory :> bytes128 (word_add htbl_p (word 80))) s = h4)
     (\s. read PC s = word (pc + 0x11cc) /\
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
          read (memory :> bytes128 xi_p) s =
          word_bytereverse
            (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
              [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2; word_bytereverse cph3]) /\
          read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 4 ctr0)
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(out_p, 64); memory :> bytes(xi_p, 16);
                 memory :> bytes(ivec_p, 16);
                 memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  CLEAR_KEEPGHALL_MEMO_TAC THEN  (* empty the normalizer fixpoint table *)
  (* split hk at htbl_p+16: the Karatsuba mids of H (low) and H^2 (high) *)
  FIRST_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 (word_add htbl_p (word 16))) s0` with _ -> false)
    then (MP_TAC th THEN PURE_ONCE_REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] THEN STRIP_TAC)
    else NO_TAC) THEN
  (* split h3k at htbl_p+64: the Karatsuba mids of H^3 (low) and H^4 (high) *)
  FIRST_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 (word_add htbl_p (word 64))) s0` with _ -> false)
    then (MP_TAC th THEN PURE_ONCE_REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] THEN STRIP_TAC)
    else NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_add (htbl_p:int64) (word 16)) (word 8) = word_add htbl_p (word 24)`;
    WORD_RULE
    `word_add (word_add (htbl_p:int64) (word 64)) (word 8) = word_add htbl_p (word 72)`]) THEN
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

(* ========================================================================= *)
(* The bridge to the band goals.  The postcondition and the frame of         *)
(* WB_FUSED_kBLOCK are those of mk_band_goal k under cph_i :=                *)
(* bytes_to_int128 (SUB_LIST (16 * i,16) ibytes); only the preconditions     *)
(* differ (the band goal reads the whole input buffer and states             *)
(* htable_mem_dec, the fused theorems read each block and each table slot),  *)
(* bridged by INPUT_BYTES_TO_BYTE128_LANES and the htable_mem_dec unfold.    *)
(* The side conditions of the fused theorems on hk, h2 .. h4 discharge by    *)
(* HK_LOW/HI_IS_KARA, karatsuba_mid and BYTESWAP128_INVOLUTION.              *)
(* ========================================================================= *)

let HK_LOW_IS_KARA = prove
 (`!a b:64 word. word_subword (word_join a b:int128) (0,64):64 word = b`,
  CONV_TAC WORD_BLAST);;
let HK_HI_IS_KARA = prove
 (`!a b:64 word. word_subword (word_join a b:int128) (64,64):64 word = a`,
  CONV_TAC WORD_BLAST);;

(* The instantiation of the fused theorems (s42_fused_specl_args k): the
   H powers as the lets of htable_mem_dec compute them (hb = byteswap128 h,
   h2 = byteswap128 (polyval_dot hb hb), h3 and h4 one more polyval_dot
   each), the packed Karatsuba mids hk and h3k, and the input blocks of
   ibytes. *)
let s42_hb_tm = `byteswap128 (h:int128)`;;
let rec s42_hdot_raw j =
  if j <= 1 then s42_hb_tm
  else mk_comb(mk_comb(`polyval_dot:int128->int128->int128`, s42_hdot_raw (j-1)), s42_hb_tm);;
let s42_hpow j = mk_comb(`byteswap128:int128->int128`, s42_hdot_raw j);;
let s42_km t = mk_comb(`karatsuba_mid`, t);;
let s42_mk_join a b = mk_comb(mk_comb(`word_join:(64)word->(64)word->int128`, a), b);;
let s42_hk_tm  = s42_mk_join (s42_km (s42_hpow 2)) (s42_km `h:int128`);;
let s42_h3k_tm = s42_mk_join (s42_km (s42_hpow 4)) (s42_km (s42_hpow 3));;
let s42_cph_tm i = subst [mk_small_numeral(16*i),`nnn:num`]
  `bytes_to_int128 (SUB_LIST (nnn,16) (ibytes:byte list))`;;
let s42_ptr_args = [`pc:num`;`stackpointer:int64`;`out_p:int64`;`xi_p:int64`;`ivec_p:int64`;
                `in_p:int64`;`key_p:int64`;`htbl_p:int64`];;
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
    MP_TAC(SPECL [nk; `in_p:int64`; `ibytes:byte list`; `x:armstate`] INPUT_BYTES_TO_BYTE128_LANES) THEN
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


(* ------------------------------------------------------------------------- *)
(* The readable band theorems and the <=8-block dispatch theorem.            *)
(*                                                                           *)
(* They follow from the BUF band theorems without simulation: only the       *)
(* presentation of the input and the output changes, by bridges that do not  *)
(* involve the machine, applied through ENSURES_PRECONDITION_THM and         *)
(* ENSURES_POSTCONDITION_THM.  The bridges come in two layers (neither is a  *)
(* named specification):                                                     *)
(*   1. byte_list_at plumbing (BYTE_LIST_AT_TO_READ_BYTES,                   *)
(*      BYTE_LIST_AT_WHOLE_CTR, prove_wb_wrapper): the per-block stores and  *)
(*      the explicit ghash_polyval_acc -> gcm_dec_pt_bytes and               *)
(*      gcm_dec_final_xi;                                                    *)
(*   2. NIST vocabulary (htable_mem_8, GCM_DEC_FINAL_XI_NIST,                *)
(*      nist_input_block_bytes): the twisted-key POLYVAL objects -> the      *)
(*      SP 800-38D nist_ghash under the free NIST hash key H, with           *)
(*      byteswap128 h = ghash_twist H.                                       *)
(* The eight AES256_GCM_DEC_ALT_{1..8}BLOCK statements are written out       *)
(* literally, as the specification.  DISPATCH covers bit_len = 128 * nblk    *)
(* for 1 <= nblk <= 8; longer inputs are the nblk > 8 proof below, and       *)
(* bit_len = 0 and the non-multiples of 128, which return 0 without touching *)
(* memory, are handled in the subroutine theorems further below.             *)
(* ------------------------------------------------------------------------- *)

(* ---- step 1: input bridge (byte_list_at -> the whole-buffer read) ---- *)
let BYTE_LIST_AT_TO_READ_BYTES = prove
 (`!bl (ptr:int64) (len:int64) s.
    byte_list_at bl ptr len s /\ LENGTH bl = val len
    ==> read (memory :> bytes (ptr, val len)) s = num_of_bytelist bl`,
  REPEAT GEN_TAC THEN REWRITE_TAC[byte_list_at] THEN STRIP_TAC THEN
  SUBGOAL_THEN `num_of_bytelist (bl:byte list) = num_of_bytelist (SUB_LIST (0, val (len:int64)) bl)` SUBST1_TAC THENL
   [AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`val (len:int64)`; `ptr:int64`; `bl:byte list`; `s:armstate`] BYTE_LIST_TO_NUM_THM) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN DISCH_THEN(fun th -> ASM_REWRITE_TAC[GSYM th]));;

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
    `read (memory :> bytes128 xi_p) s = gcm_dec_final_xi nnn ibytes xi h` in
  (* the counter write-back conjunct of the band, unchanged *)
  let ivecpost = mk_ivec_conj k in
  let post' = mk_abs(sv, list_mk_conj [pcc; x9c; outpost; xipost; ivecpost]) in
  list_mk_forall(vars,
    mk_imp(hyps, list_mk_comb(rator(rator(rator ens)), [pre'; post'; frame])));;

let ghash_wholes = [GCM_DEC_GHASH_BLOCKS_WHOLE_1;GCM_DEC_GHASH_BLOCKS_WHOLE_2;
                    GCM_DEC_GHASH_BLOCKS_WHOLE_3;GCM_DEC_GHASH_BLOCKS_WHOLE_4;
                    GCM_DEC_GHASH_BLOCKS_WHOLE_5;GCM_DEC_GHASH_BLOCKS_WHOLE_6;
                    GCM_DEC_GHASH_BLOCKS_WHOLE_7;GCM_DEC_GHASH_BLOCKS_WHOLE_8];;
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

(* ------------------------------------------------------------------------- *)
(* NIST-vocabulary bridge layer (the statement shape of the 4-way kernels).  *)
(*   - htable_mem_8: htable_mem_4-style named memory predicate over h_power  *)
(*     indexing, for the 12-slot AWS-LC key table (packed Karatsuba mids).   *)
(*   - GCM_DEC_FINAL_XI_NIST: gcm_dec_final_xi = byte-reversed nist_ghash    *)
(*     under byteswap128 h = ghash_twist H (Gueron Prop 1 via                *)
(*     NIST_GHASH_IS_POLYVAL from common/ghash_nist_bridge.ml).              *)
(*   - nist_input_block_bytes: the NIST (big-endian) view of input block i   *)
(*     of a byte list, with the LIST_OF_SEQ_NIST_INPUT bridges to            *)
(*     gcm_dec_ghash_blocks.                                                 *)
(*   - wordlist_from_memory key condensation: KEY_READS_FROM_WORDLIST and    *)
(*     RK_ETA_15 relate the round-key list rk to the 15 bytes128 key reads.  *)
(* ------------------------------------------------------------------------- *)

(* ---- karatsuba_mid ignores the byteswap of its argument ---- *)
let KARATSUBA_MID_BYTESWAP = prove
 (`!x:int128. karatsuba_mid (byteswap128 x) = karatsuba_mid x`,
  GEN_TAC THEN REWRITE_TAC[karatsuba_mid; byteswap128] THEN
  CONV_TAC WORD_BLAST);;

(* ---- h_power 0..7 unfolded to the explicit left-nested dot chains ---- *)
let H_POWER_UNFOLD_7 = prove
 (`h_power (hb:int128) 0 = hb /\
   h_power hb 1 = polyval_dot hb hb /\
   h_power hb 2 = polyval_dot (polyval_dot hb hb) hb /\
   h_power hb 3 = polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb /\
   h_power hb 4 = polyval_dot (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) hb /\
   h_power hb 5 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) hb) hb /\
   h_power hb 6 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) hb) hb) hb /\
   h_power hb 7 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) hb) hb) hb) hb`,
  REWRITE_TAC[num_CONV `7`; num_CONV `6`; num_CONV `5`; num_CONV `4`;
              num_CONV `3`; num_CONV `2`; num_CONV `1`; h_power]);;

(* ---- htable_mem_dec in h_power form, without the nested lets ---- *)
let HTABLE_MEM_DEC_H_POWER = prove
 (`!(h:int128) (ptr:int64) (s:armstate).
     htable_mem_dec h ptr s <=>
     read (memory :> bytes128 ptr) s = byteswap128 (h_power (byteswap128 h) 0) /\
     read (memory :> bytes128 (word_add ptr (word 16))) s =
       word_join (karatsuba_mid (h_power (byteswap128 h) 1))
                 (karatsuba_mid (h_power (byteswap128 h) 0)) /\
     read (memory :> bytes128 (word_add ptr (word 32))) s = byteswap128 (h_power (byteswap128 h) 1) /\
     read (memory :> bytes128 (word_add ptr (word 48))) s = byteswap128 (h_power (byteswap128 h) 2) /\
     read (memory :> bytes128 (word_add ptr (word 64))) s =
       word_join (karatsuba_mid (h_power (byteswap128 h) 3))
                 (karatsuba_mid (h_power (byteswap128 h) 2)) /\
     read (memory :> bytes128 (word_add ptr (word 80))) s = byteswap128 (h_power (byteswap128 h) 3) /\
     read (memory :> bytes128 (word_add ptr (word 96))) s = byteswap128 (h_power (byteswap128 h) 4) /\
     read (memory :> bytes128 (word_add ptr (word 112))) s =
       word_join (karatsuba_mid (h_power (byteswap128 h) 5))
                 (karatsuba_mid (h_power (byteswap128 h) 4)) /\
     read (memory :> bytes128 (word_add ptr (word 128))) s = byteswap128 (h_power (byteswap128 h) 5) /\
     read (memory :> bytes128 (word_add ptr (word 144))) s = byteswap128 (h_power (byteswap128 h) 6) /\
     read (memory :> bytes128 (word_add ptr (word 160))) s =
       word_join (karatsuba_mid (h_power (byteswap128 h) 7))
                 (karatsuba_mid (h_power (byteswap128 h) 6)) /\
     read (memory :> bytes128 (word_add ptr (word 176))) s = byteswap128 (h_power (byteswap128 h) 7)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[htable_mem_dec] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[H_POWER_UNFOLD_7; KARATSUBA_MID_BYTESWAP; BYTESWAP128_INVOLUTION]);;

(* ---- the named key-table predicate over the abstract key hk ---- *)
(* htable_mem_8 hk ptr s is the shared predicate of aes_gcm_spec.ml, and
   HTABLE_MEM_8_FLAT (aes_gcm_common.ml) states it as 12 flat conjuncts.
   hk is the POLYVAL-side key (byteswap128 of the h slot in memory); with
   hk = ghash_twist H this is the analogue of the htable_mem_4 (ghash_twist
   ...) hypothesis of the 4-way kernels, extended to 8 powers and 12 slots
   (the AWS-LC layout with packed Karatsuba mids). *)
let HTABLE_MEM_DEC_IS_HTABLE_MEM_8 = prove
 (`!(h:int128) (ptr:int64) (s:armstate).
     htable_mem_dec h ptr s <=> htable_mem_8 (byteswap128 h) ptr s`,
  REWRITE_TAC[HTABLE_MEM_DEC_H_POWER; HTABLE_MEM_8_FLAT]);;

(* word_bytereverse = word_reversefields 8 at :128. *)
let BREV_RF8_128 = prove
 (`word_bytereverse (x:int128) = word_reversefields 8 x`,
  REWRITE_TAC[REWRITE_RULE[FUN_EQ_THM] WORD_BYTEREVERSE_REVERSEFIELDS]);;

let BREV_RF8_INV_128 = prove
 (`!x:int128. word_bytereverse (word_reversefields 8 x) = x`,
  REWRITE_TAC[GSYM BREV_RF8_128; WORD_BYTEREVERSE_BYTEREVERSE]);;

(* ---- the tag spec in nist_ghash vocabulary ---- *)
(* The band statements quantify the raw h slot of the key table; the 4-way
   kernels quantify the NIST key H with the twist applied in the hypothesis.
   The two are related by byteswap128 h = ghash_twist H, under which
   gcm_dec_final_xi is a byte-reversed nist_ghash (Gueron Prop 1 via
   NIST_GHASH_IS_POLYVAL). *)
let GCM_DEC_FINAL_XI_NIST = prove
 (`!(H:int128) (h:int128) len x xi.
     byteswap128 h = ghash_twist H
     ==> gcm_dec_final_xi len x xi h =
         word_bytereverse
           (nist_ghash H (word_bytereverse xi)
              (MAP word_bytereverse (gcm_dec_ghash_blocks len x)))`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[gcm_dec_final_xi; NIST_GHASH_IS_POLYVAL]);;

(* ---- the NIST (big-endian) view of input block i ---- *)
let nist_input_block_bytes = new_definition
 `nist_input_block_bytes (x:byte list) (i:num) : int128 =
    word_reversefields 8 (bytes_to_int128 (SUB_LIST (16 * i, 16) x))`;;

(* list_of_seq (nist_input_block_bytes x) N =
   MAP word_bytereverse (gcm_dec_ghash_blocks (16*N) x) *)
let build_list_of_seq_nist n =
  let goal = list_mk_forall([`x:byte list`],
    mk_eq(list_mk_comb(`list_of_seq:(num->int128)->num->int128 list`,
            [mk_comb(`nist_input_block_bytes`,`x:byte list`); mk_small_numeral n]),
          mk_comb(`MAP (word_bytereverse:int128->int128)`,
            list_mk_comb(`gcm_dec_ghash_blocks`, [mk_small_numeral(16*n);`x:byte list`])))) in
  prove(goal,
    GEN_TAC THEN REWRITE_TAC[el (n-1) ghash_wholes; MAP] THEN
    REWRITE_TAC(map num_CONV (map mk_small_numeral (rev(1--n)))) THEN
    REWRITE_TAC[LIST_OF_SEQ; o_DEF; nist_input_block_bytes; BREV_RF8_128] THEN
    CONV_TAC NUM_REDUCE_CONV);;
let LIST_OF_SEQ_NIST_INPUT = map build_list_of_seq_nist (1--8);;

(* ---- key condensation: the round-key list and its 15 bytes128 reads ---- *)
let RK_ETA_15 = prove
 (`!rk:int128 list. LENGTH rk = 15
     ==> rk = [EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
               EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk; EL 11 rk; EL 12 rk;
               EL 13 rk; EL 14 rk]`,
  GEN_TAC THEN REWRITE_TAC[LENGTH_EQ_LIST_OF_SEQ] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
  REWRITE_TAC(map num_CONV (map mk_small_numeral (rev(1--15)))) THEN
  REWRITE_TAC[LIST_OF_SEQ; o_DEF] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let KEY_READS_FROM_WORDLIST = prove
 (`!(key_p:int64) (rk:int128 list) s.
     wordlist_from_memory (key_p,15) s = rk
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
         read (memory :> bytes128 (word_add key_p (word 160))) s = EL 10 rk /\
         read (memory :> bytes128 (word_add key_p (word 176))) s = EL 11 rk /\
         read (memory :> bytes128 (word_add key_p (word 192))) s = EL 12 rk /\
         read (memory :> bytes128 (word_add key_p (word 208))) s = EL 13 rk /\
         read (memory :> bytes128 (word_add key_p (word 224))) s = EL 14 rk`,
  REPEAT GEN_TAC THEN
  CONV_TAC(LAND_CONV(LAND_CONV WORDLIST_FROM_MEMORY_CONV)) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC(map num_CONV (map mk_small_numeral (rev(1--14)))) THEN
  REWRITE_TAC[EL; HD; TL]);;

(* byteswap128 (byteswap128 (ghash_twist H)) = ghash_twist H, for the
   instantiation h := byteswap128 (ghash_twist H). *)
let bsw_inv = SPEC `ghash_twist H` BYTESWAP128_INVOLUTION;;
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
  let winst = SPECL ([`pc:num`;`stackpointer:int64`;`out_p:int64`;`xi_p:int64`;`ivec_p:int64`;
                      `in_p:int64`;`key_p:int64`;`htbl_p:int64`;`ibytes:byte list`;
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
(* XORed onto the input bytes (gcm_dec_pt_bytes), replaces the tag at xi_p   *)
(* with the SP 800-38D GHASH of the N raw ciphertext blocks folded onto tag0 *)
(* under the NIST hash key H (both tag values byte-reversed, as the AWS-LC   *)
(* caller keeps them), stores the counter block advanced by N at ivec_p      *)
(* (gcm_ctr_inc_iter N ctr0), and leaves the byte count 16 * N in X9.        *)
(* ------------------------------------------------------------------------- *)

let AES256_GCM_DEC_ALT_1BLOCK = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 16 /\ LENGTH rk = 15 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,16; xi_p,16; ivec_p,16]
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,16; key_p,240; htbl_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,16; xi_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,16; key_p,240; htbl_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 128; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
               byte_list_at ibytes in_p (word 16) s /\
               read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,15) s = rk /\
               htable_mem_8 (ghash_twist H) htbl_p s)
          (\s. read PC s = word (pc + 4556) /\
               read X9 s = word 16 /\
               byte_list_at (gcm_dec_pt_bytes 16 ibytes ctr0 rk) out_p (word 16) s /\
               read (memory :> bytes128 xi_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block_bytes ibytes) 1))
               /\
               read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 1 ctr0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out_p,16); memory :> bytes(xi_p,16);
                      memory :> bytes(ivec_p,16);
                      memory :> bytes(word_add stackpointer (word 64),16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  WB_READABLE_TAC 1 AES256_GCM_DEC_ALT_BUF_1BLOCK);;

let AES256_GCM_DEC_ALT_2BLOCK = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 32 /\ LENGTH rk = 15 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,32; xi_p,16; ivec_p,16]
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,32; key_p,240; htbl_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,32; xi_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,32; key_p,240; htbl_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 256; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
               byte_list_at ibytes in_p (word 32) s /\
               read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,15) s = rk /\
               htable_mem_8 (ghash_twist H) htbl_p s)
          (\s. read PC s = word (pc + 4556) /\
               read X9 s = word 32 /\
               byte_list_at (gcm_dec_pt_bytes 32 ibytes ctr0 rk) out_p (word 32) s /\
               read (memory :> bytes128 xi_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block_bytes ibytes) 2))
               /\
               read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 2 ctr0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out_p,32); memory :> bytes(xi_p,16);
                      memory :> bytes(ivec_p,16);
                      memory :> bytes(word_add stackpointer (word 64),16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  WB_READABLE_TAC 2 AES256_GCM_DEC_ALT_BUF_2BLOCK);;

let AES256_GCM_DEC_ALT_3BLOCK = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 48 /\ LENGTH rk = 15 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,48; xi_p,16; ivec_p,16]
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,48; key_p,240; htbl_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,48; xi_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,48; key_p,240; htbl_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 384; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
               byte_list_at ibytes in_p (word 48) s /\
               read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,15) s = rk /\
               htable_mem_8 (ghash_twist H) htbl_p s)
          (\s. read PC s = word (pc + 4556) /\
               read X9 s = word 48 /\
               byte_list_at (gcm_dec_pt_bytes 48 ibytes ctr0 rk) out_p (word 48) s /\
               read (memory :> bytes128 xi_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block_bytes ibytes) 3))
               /\
               read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 3 ctr0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out_p,48); memory :> bytes(xi_p,16);
                      memory :> bytes(ivec_p,16);
                      memory :> bytes(word_add stackpointer (word 64),16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  WB_READABLE_TAC 3 AES256_GCM_DEC_ALT_BUF_3BLOCK);;

let AES256_GCM_DEC_ALT_4BLOCK = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 64 /\ LENGTH rk = 15 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,64; xi_p,16; ivec_p,16]
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,64; key_p,240; htbl_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,64; xi_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,64; key_p,240; htbl_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 512; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
               byte_list_at ibytes in_p (word 64) s /\
               read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,15) s = rk /\
               htable_mem_8 (ghash_twist H) htbl_p s)
          (\s. read PC s = word (pc + 4556) /\
               read X9 s = word 64 /\
               byte_list_at (gcm_dec_pt_bytes 64 ibytes ctr0 rk) out_p (word 64) s /\
               read (memory :> bytes128 xi_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block_bytes ibytes) 4))
               /\
               read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 4 ctr0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out_p,64); memory :> bytes(xi_p,16);
                      memory :> bytes(ivec_p,16);
                      memory :> bytes(word_add stackpointer (word 64),16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  WB_READABLE_TAC 4 AES256_GCM_DEC_ALT_BUF_4BLOCK);;

let AES256_GCM_DEC_ALT_5BLOCK = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 80 /\ LENGTH rk = 15 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,80; xi_p,16; ivec_p,16]
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,80; key_p,240; htbl_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,80; xi_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,80; key_p,240; htbl_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 640; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
               byte_list_at ibytes in_p (word 80) s /\
               read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,15) s = rk /\
               htable_mem_8 (ghash_twist H) htbl_p s)
          (\s. read PC s = word (pc + 4556) /\
               read X9 s = word 80 /\
               byte_list_at (gcm_dec_pt_bytes 80 ibytes ctr0 rk) out_p (word 80) s /\
               read (memory :> bytes128 xi_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block_bytes ibytes) 5))
               /\
               read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 5 ctr0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out_p,80); memory :> bytes(xi_p,16);
                      memory :> bytes(ivec_p,16);
                      memory :> bytes(word_add stackpointer (word 64),16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  WB_READABLE_TAC 5 AES256_GCM_DEC_ALT_BUF_5BLOCK);;

let AES256_GCM_DEC_ALT_6BLOCK = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 96 /\ LENGTH rk = 15 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,96; xi_p,16; ivec_p,16]
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,96; key_p,240; htbl_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,96; xi_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,96; key_p,240; htbl_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 768; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
               byte_list_at ibytes in_p (word 96) s /\
               read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,15) s = rk /\
               htable_mem_8 (ghash_twist H) htbl_p s)
          (\s. read PC s = word (pc + 4556) /\
               read X9 s = word 96 /\
               byte_list_at (gcm_dec_pt_bytes 96 ibytes ctr0 rk) out_p (word 96) s /\
               read (memory :> bytes128 xi_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block_bytes ibytes) 6))
               /\
               read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 6 ctr0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out_p,96); memory :> bytes(xi_p,16);
                      memory :> bytes(ivec_p,16);
                      memory :> bytes(word_add stackpointer (word 64),16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  WB_READABLE_TAC 6 AES256_GCM_DEC_ALT_BUF_6BLOCK);;

let AES256_GCM_DEC_ALT_7BLOCK = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 112 /\ LENGTH rk = 15 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,112; xi_p,16; ivec_p,16]
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,112; key_p,240; htbl_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,112; xi_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,112; key_p,240; htbl_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 896; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
               byte_list_at ibytes in_p (word 112) s /\
               read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,15) s = rk /\
               htable_mem_8 (ghash_twist H) htbl_p s)
          (\s. read PC s = word (pc + 4556) /\
               read X9 s = word 112 /\
               byte_list_at (gcm_dec_pt_bytes 112 ibytes ctr0 rk) out_p (word 112) s /\
               read (memory :> bytes128 xi_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block_bytes ibytes) 7))
               /\
               read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 7 ctr0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out_p,112); memory :> bytes(xi_p,16);
                      memory :> bytes(ivec_p,16);
                      memory :> bytes(word_add stackpointer (word 64),16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  WB_READABLE_TAC 7 AES256_GCM_DEC_ALT_BUF_7BLOCK);;

let AES256_GCM_DEC_ALT_8BLOCK = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 128 /\ LENGTH rk = 15 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,128; xi_p,16; ivec_p,16]
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,128; key_p,240; htbl_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,128; xi_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,128; key_p,240; htbl_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 1024; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
               byte_list_at ibytes in_p (word 128) s /\
               read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,15) s = rk /\
               htable_mem_8 (ghash_twist H) htbl_p s)
          (\s. read PC s = word (pc + 4556) /\
               read X9 s = word 128 /\
               byte_list_at (gcm_dec_pt_bytes 128 ibytes ctr0 rk) out_p (word 128) s /\
               read (memory :> bytes128 xi_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block_bytes ibytes) 8))
               /\
               read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 8 ctr0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out_p,128); memory :> bytes(xi_p,16);
                      memory :> bytes(ivec_p,16);
                      memory :> bytes(word_add stackpointer (word 64),16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  WB_READABLE_TAC 8 AES256_GCM_DEC_ALT_BUF_8BLOCK);;

(* ---- the <=8-block dispatch theorem ----
   One readable theorem for every whole-blocks call with 1 <= nblk <= 8:
   symbolic nblk, the C argument bit_len = word (128 * nblk), byte_list_at
   input and output over the whole 16 * nblk-byte buffer, and the NIST
   vocabulary of the bands.  Proof: a case split on nblk; each case reduces
   16 * k and 128 * k to numerals and applies the band theorem. *)
let AES256_GCM_DEC_ALT_DISPATCH = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p
    nblk ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     1 <= nblk /\ nblk <= 8 /\
     LENGTH ibytes = 16 * nblk /\ LENGTH rk = 15 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,16 * nblk; xi_p,16; ivec_p,16]
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,240; htbl_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,240; htbl_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word (128 * nblk); out_p; xi_p; ivec_p; key_p; htbl_p] s /\
               byte_list_at ibytes in_p (word (16 * nblk)) s /\
               read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,15) s = rk /\
               htable_mem_8 (ghash_twist H) htbl_p s)
          (\s. read PC s = word (pc + 4556) /\
               read X9 s = word (16 * nblk) /\
               byte_list_at (gcm_dec_pt_bytes (16 * nblk) ibytes ctr0 rk) out_p (word (16 * nblk)) s /\
               read (memory :> bytes128 xi_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block_bytes ibytes) nblk))
               /\
               read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter nblk ctr0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out_p,16 * nblk); memory :> bytes(xi_p,16);
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

(* exact ival of an in-range pointer offset (for the signed pointer compares
   cmp x0,x5 at 0x3fc/0x45c/0xa00 feeding b.ge/b.lt) *)
let IVAL_PTR_ADD = prove
 (`!(p:int64) a. val p + a < 2 EXP 63 ==> ival (word_add p (word a)) = &(val p + a)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_add p (word a):int64 = word (val p + a)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC MOD_DOWN_CONV THEN REFL_TAC; ALL_TAC] THEN
  MATCH_MP_TAC IVAL_WORD_LT THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC);;

(* ival (word_neg (word d)) = -- &d needs d <= 2^63 *)
let IVAL_NEG_SMALL = prove
 (`!d. d <= 2 EXP 63 ==> ival (word_neg (word d):int64) = -- &d`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[WORD_IWORD] THEN
  REWRITE_TAC[GSYM IWORD_INT_NEG] THEN MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[INT_ARITH `--(&9223372036854775808):int <= -- &d /\ -- &d < &9223372036854775808 <=> &d <= &9223372036854775808`] THEN
  ASM_REWRITE_TAC[INT_OF_NUM_LE] THEN ASM_ARITH_TAC);;

(* signed sub of two small words *)
let IVAL_WSUB_SMALL = prove
 (`!a d. a < 2 EXP 63 /\ d < 2 EXP 63
      ==> ival (word_sub (word a) (word d):int64) = &a - &d`,
  REPEAT STRIP_TAC THEN
  DISJ_CASES_TAC(ARITH_RULE `a < d \/ d <= a:num`) THENL
   [SUBGOAL_THEN `word_sub (word a) (word d):int64 = word_neg (word (d - a))` SUBST1_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [WORD_RULE `word_sub (word a) (word d):int64 = word_neg (word_sub (word d) (word a))`] THEN
      AP_TERM_TAC THEN REWRITE_TAC[WORD_SUB] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `ival (word_neg (word (d - a)):int64) = -- &(d - a)` SUBST1_TAC THENL
     [MATCH_MP_TAC IVAL_NEG_SMALL THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&(d - a):int = &d - &a` SUBST1_TAC THENL
     [REWRITE_TAC[INT_OF_NUM_SUB] THEN ASM_ARITH_TAC; INT_ARITH_TAC];
    SUBGOAL_THEN `word_sub (word a) (word d):int64 = word (a - d)` SUBST1_TAC THENL
     [REWRITE_TAC[WORD_SUB] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `ival (word (a - d):int64) = &(a - d)` SUBST1_TAC THENL
     [MATCH_MP_TAC IVAL_WORD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&(a - d):int = &a - &d` SUBST1_TAC THENL
     [REWRITE_TAC[INT_OF_NUM_SUB] THEN ASM_ARITH_TAC; INT_ARITH_TAC]]);;

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
   [MATCH_MP_TAC IVAL_WSUB_SMALL THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
  REWRITE_TAC[INT_ARITH `(&v + &a) - (&v + &d):int = &a - &d`] THEN
  REWRITE_TAC[INT_ARITH `&a - &d:int < &0 <=> &a:int < &d`; INT_OF_NUM_LT]);;

(* d = 128*((nblk-1) DIV 8) > 128 for nblk >= 17 (the main-loop skip b.ge then
   falls through) *)
let D_GT_128 = prove
 (`!nblk. 17 <= nblk ==> (128 < 128 * (nblk - 1) DIV 8 <=> T)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(ARITH_RULE `2 <= q ==> 128 < 128 * q`) THEN
  SUBGOAL_THEN `16 <= nblk - 1` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN ASM_ARITH_TAC);;

(* The raw counter absorbs a prior gcm_ctr_add into its offset:
      gcm_ctr_raw v (gcm_ctr_add u x) = gcm_ctr_raw (word_add u v) x
   (GCM_CTR_RAW_ABSORB below, with the lane lemmas it needs; gcm_ctr_raw_def is
   defined before wb_front_postcond, whose Q30 conjunct uses it).
   INNER_TAIL_FEED_TAC uses its numeral form GCM_CTR_RAW_ABSORB_NUM to match
   the shifted tail's Q30 precondition (the shift sets ctr0 :=
   gcm_ctr_add (word (8*(q+1))) ctr0) against the seam's Q30.  The proof works
   lane by lane: gcm_ctr_raw reads only the four 32-bit lanes of its argument
   and gcm_ctr_add changes only the lane (96,32), so the low three lanes pass
   through and the top lane composes the two adds; no blast meets the symbolic
   32-bit addend. *)
let BREV_LANE_64 = prove
 (`!ctr0:int128.
     word_join (word_join (word_subword ctr0 (64,8):8 word) (word_subword ctr0 (72,8):8 word):16 word)
       (word_join (word_subword ctr0 (80,8):8 word) (word_subword ctr0 (88,8):8 word):16 word) =
     word_bytereverse (word_subword ctr0 (64,32):32 word)`,
  GEN_TAC THEN BITBLAST_TAC);;

let BREV_LANE_32 = prove
 (`!ctr0:int128.
     word_join (word_join (word_subword ctr0 (32,8):8 word) (word_subword ctr0 (40,8):8 word):16 word)
       (word_join (word_subword ctr0 (48,8):8 word) (word_subword ctr0 (56,8):8 word):16 word) =
     word_bytereverse (word_subword ctr0 (32,32):32 word)`,
  GEN_TAC THEN BITBLAST_TAC);;

let BREV_LANE_0 = prove
 (`!ctr0:int128.
     word_join (word_join (word_subword ctr0 (0,8):8 word) (word_subword ctr0 (8,8):8 word):16 word)
       (word_join (word_subword ctr0 (16,8):8 word) (word_subword ctr0 (24,8):8 word):16 word) =
     word_bytereverse (word_subword ctr0 (0,32):32 word)`,
  GEN_TAC THEN BITBLAST_TAC);;

(* gcm_ctr_raw in 32-bit-lane form: top lane = word_add(brev of z top lane) w,
   the other three lanes = byte-reverse of z's lanes. *)
let GCM_CTR_RAW_LANEFORM = prove
 (`!w z:int128. gcm_ctr_raw w z =
    word_join
     (word_join (word_add (word_bytereverse (word_subword z (96,32):32 word)) w)
                (word_bytereverse (word_subword z (64,32):32 word)):64 word)
     (word_join (word_bytereverse (word_subword z (32,32):32 word))
                (word_bytereverse (word_subword z (0,32):32 word)):64 word):int128`,
  REWRITE_TAC[gcm_ctr_raw_def] THEN
  REWRITE_TAC[GSYM BREV_TOP_LANE; GSYM BREV_LANE_64; GSYM BREV_LANE_32; GSYM BREV_LANE_0]);;

(* the low 3 lanes are unaffected by an insert into the top 32-bit lane *)
let SUBWORD_INSERT_LOW_LANE = prove
 (`!(x:int128) (nw:32 word).
     (word_subword (word_insert x (96,32) nw : int128) (0,32):32 word = word_subword x (0,32)) /\
     (word_subword (word_insert x (96,32) nw : int128) (32,32):32 word = word_subword x (32,32)) /\
     (word_subword (word_insert x (96,32) nw : int128) (64,32):32 word = word_subword x (64,32))`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN BITBLAST_TAC);;

let GCM_CTR_RAW_ABSORB = prove
 (`!(u:32 word) (v:32 word) (x:int128).
     gcm_ctr_raw v (gcm_ctr_add u x) = gcm_ctr_raw (word_add u v) x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GCM_CTR_RAW_LANEFORM] THEN
  REWRITE_TAC[gcm_ctr_add] THEN
  REWRITE_TAC[SUBWORD_INSERT_TOP; SUBWORD_INSERT_LOW_LANE; BREV_BREV_32] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC]);;

let GCM_CTR_RAW_ABSORB_NUM = prove
 (`!a b (x:int128).
     gcm_ctr_raw (word b) (gcm_ctr_add (word a) x) = gcm_ctr_raw (word (a + b)) x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GCM_CTR_RAW_ABSORB] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

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

(* pure-arith closer for the nblk >= 17 side conditions *)
let NBLK_ARITH_TAC =
  MP_TAC(ASSUME `17 <= nblk`) THEN MP_TAC(ASSUME `128 * nblk < 2 EXP 64`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;;

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

(* pure-arith closer for the union-band side conditions *)
let NBLK_ARITH_GE9_TAC =
  MP_TAC(ASSUME `9 <= nblk`) THEN
  MP_TAC(ASSUME `128 * nblk < 2 EXP 64`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;;

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
   `read X3 s = xi_p`;
   `read X6 s = htbl_p`] @
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
      INPUT_BYTES_TO_BYTE128_LANES) THEN
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
    (xi_p:int64) (ivec_p:int64) (key_p:int64) (htbl_p:int64) (stackpointer:int64)
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
    read X6 s = htbl_p /\
    read X3 s = xi_p /\
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
    htable_mem_dec h htbl_p s`;;

(* ------------------------------------------------------------------------- *)
(* 5. GHASH 8-block extension algebra (no simulation).                       *)
(*                                                                           *)
(* The invariant's Q19 is the byte-reversed GHASH fold                       *)
(*   ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)                 *)
(*     (MAP word_bytereverse (list_of_seq blk (8 * i)))                      *)
(* over the raw ciphertext blocks blk k =                                    *)
(* bytes_to_int128 (SUB_LIST (16*k,16) ibytes), k < 8i.  The loop body and   *)
(* the prepretail each fold one more 8-block group (blocks 8i..8i+7, one     *)
(* Horner step per block, each block byte-reversed and XORed into the        *)
(* accumulator), so the fold over 8(i+1) blocks must equal the fold over 8i  *)
(* blocks continued by the 8 Horner steps, in the machine's 8-block          *)
(* byteform.  This is list algebra over GHASH_ACC_APPEND                     *)
(* (common/polyval_ghash.ml) and list_of_seq.                                *)
(* ------------------------------------------------------------------------- *)

(* list_of_seq splits at any offset (APPEND-at-end recursion, induct on n) *)
let LIST_OF_SEQ_SPLIT = prove
 (`!(f:num->int128) m n. list_of_seq f (m + n) =
     APPEND (list_of_seq f m) (list_of_seq (\j. f (m + j)) n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; list_of_seq; APPEND_NIL] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; list_of_seq; APPEND_ASSOC]);;

(* generic group-extension of the byte-reversed GHASH fold: split m+n *)
let GHASH_ACC_GROUP_EXTEND = prove
 (`!(g:num->int128) H acc m n.
    ghash_polyval_acc H acc (MAP word_bytereverse (list_of_seq g (m + n))) =
    ghash_polyval_acc H
      (ghash_polyval_acc H acc (MAP word_bytereverse (list_of_seq g m)))
      (MAP word_bytereverse (list_of_seq (\j. g (m + j)) n))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LIST_OF_SEQ_SPLIT; MAP_APPEND; GHASH_ACC_APPEND]);;

(* clean 8-element unfold of list_of_seq (numerals, no SUC towers) *)
let LIST_OF_SEQ_8 = prove
 (`!f:num->int128. list_of_seq f 8 =
    [f 0; f 1; f 2; f 3; f 4; f 5; f 6; f 7]`,
  GEN_TAC THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[num_CONV `8`; num_CONV `7`; num_CONV `6`;
    num_CONV `5`; num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`;
    LIST_OF_SEQ])) THEN
  REWRITE_TAC[o_THM] THEN CONV_TAC(DEPTH_CONV NUM_SUC_CONV) THEN REWRITE_TAC[]);;

(* The main lemma: extend the invariant's GHASH fold by one 8-block group.   *)
(* The right-hand side is the 8*i fold continued by a fold over the 8 new    *)
(* raw ciphertext blocks 8*i .. 8*i+7.  BODY_Q19_CLOSE_ALGEBRA rewrites with *)
(* it, at blk := \k. bytes_to_int128 (SUB_LIST (16*k,16) ibytes).            *)
let GHASH_ACC_8BLOCK_EXTEND = prove
 (`!(blk:num->int128) H acc i.
    ghash_polyval_acc H acc
      (MAP word_bytereverse (list_of_seq blk (8 * (i + 1)))) =
    ghash_polyval_acc H
      (ghash_polyval_acc H acc (MAP word_bytereverse (list_of_seq blk (8 * i))))
      (MAP word_bytereverse
        [blk (8 * i); blk (8 * i + 1); blk (8 * i + 2); blk (8 * i + 3);
         blk (8 * i + 4); blk (8 * i + 5); blk (8 * i + 6); blk (8 * i + 7)])`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `8 * (i + 1) = 8 * i + 8` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GHASH_ACC_GROUP_EXTEND] THEN
  REWRITE_TAC[LIST_OF_SEQ_8] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ADD_CLAUSES]);;

(* The body GHASH-close bridge: spec_to_byteform_wb8 of the <=8-block chain  *)
(* generalized from the tail's incoming accumulator word_bytereverse xi to   *)
(* an arbitrary one, acc (the running fold that Q19 holds at the start of    *)
(* the loop body).  The H-power hypotheses and the machine byteform on the   *)
(* right are the same, and so is the proof (GHASH_POLYVAL_ACC_8, the         *)
(* hypotheses, WORD_RULE), which does not depend on the accumulator being    *)
(* xi.  BODY_Q19_CLOSE_ALGEBRA composes it with GHASH_ACC_8BLOCK_EXTEND      *)
(* (acc := the invariant's 8*i fold) to close the loop body's Q19.           *)
let SPEC_TO_BYTEFORM_WB8_ACC = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 =
   polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 =
   polyval_dot
   (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
   (byteswap128 h) /\
   byteswap128 h5 =
   polyval_dot
   (polyval_dot
    (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
    (byteswap128 h))
   (byteswap128 h) /\
   byteswap128 h6 =
   polyval_dot
   (polyval_dot
    (polyval_dot
     (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
     (byteswap128 h))
    (byteswap128 h))
   (byteswap128 h) /\
   byteswap128 h7 =
   polyval_dot
   (polyval_dot
    (polyval_dot
     (polyval_dot
      (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
      (byteswap128 h))
     (byteswap128 h))
    (byteswap128 h))
   (byteswap128 h) /\
   byteswap128 h8 =
   polyval_dot
   (polyval_dot
    (polyval_dot
     (polyval_dot
      (polyval_dot
       (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
       (byteswap128 h))
      (byteswap128 h))
     (byteswap128 h))
    (byteswap128 h))
   (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (acc:int128)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
        word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5;
        word_bytereverse cph6; word_bytereverse cph7] =
       polyval_reduce_prop3
       (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
        (word_pmul (word_xor acc (word_bytereverse cph0)) (byteswap128 h8))
        (word_pmul (word_bytereverse cph1) (byteswap128 h7)))
        (word_pmul (word_bytereverse cph2) (byteswap128 h6)))
        (word_pmul (word_bytereverse cph3) (byteswap128 h5)))
        (word_pmul (word_bytereverse cph4) (byteswap128 h4)))
        (word_pmul (word_bytereverse cph5) (byteswap128 h3)))
        (word_pmul (word_bytereverse cph6) (byteswap128 h2)))
       (word_pmul (word_bytereverse cph7) (byteswap128 h)))`,
  STRIP_TAC THEN REWRITE_TAC[GHASH_POLYVAL_ACC_8] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* The composed Q19 close of the loop body: the invariant's Q19 conjunct at  *)
(* i+1 equals the machine 8-block byteform with the invariant's own 8*i fold *)
(* as the incoming accumulator, by GHASH_ACC_8BLOCK_EXTEND (the 8*(i+1) fold *)
(* as the 8 new blocks on top of the 8*i fold) and SPEC_TO_BYTEFORM_WB8_ACC  *)
(* (acc := that 8*i fold).  The whole GHASH algebra of the body close is     *)
(* settled here, without simulation; build_q19_reduce_clean and              *)
(* build_q19_reduce_clean_idx (below) instantiate it for the Q19 closes of   *)
(* the loop body and the prepretail.                                         *)
let BODY_Q19_CLOSE_ALGEBRA = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 =
   polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 =
   polyval_dot
   (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
   (byteswap128 h) /\
   byteswap128 h5 =
   polyval_dot
   (polyval_dot
    (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
    (byteswap128 h))
   (byteswap128 h) /\
   byteswap128 h6 =
   polyval_dot
   (polyval_dot
    (polyval_dot
     (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
     (byteswap128 h))
    (byteswap128 h))
   (byteswap128 h) /\
   byteswap128 h7 =
   polyval_dot
   (polyval_dot
    (polyval_dot
     (polyval_dot
      (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
      (byteswap128 h))
     (byteswap128 h))
    (byteswap128 h))
   (byteswap128 h) /\
   byteswap128 h8 =
   polyval_dot
   (polyval_dot
    (polyval_dot
     (polyval_dot
      (polyval_dot
       (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
       (byteswap128 h))
      (byteswap128 h))
     (byteswap128 h))
    (byteswap128 h))
   (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        (MAP word_bytereverse
         (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes))
          (8 * (i+1)))) =
        polyval_reduce_prop3
        (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
         (word_pmul (word_xor (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
           (MAP word_bytereverse
            (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes)) (8 * i))))
           (word_bytereverse (bytes_to_int128 (SUB_LIST (16*(8*i+0),16) ibytes)))) (byteswap128 h8))
         (word_pmul (word_bytereverse (bytes_to_int128 (SUB_LIST (16*(8*i+1),16) ibytes))) (byteswap128 h7)))
         (word_pmul (word_bytereverse (bytes_to_int128 (SUB_LIST (16*(8*i+2),16) ibytes))) (byteswap128 h6)))
         (word_pmul (word_bytereverse (bytes_to_int128 (SUB_LIST (16*(8*i+3),16) ibytes))) (byteswap128 h5)))
         (word_pmul (word_bytereverse (bytes_to_int128 (SUB_LIST (16*(8*i+4),16) ibytes))) (byteswap128 h4)))
         (word_pmul (word_bytereverse (bytes_to_int128 (SUB_LIST (16*(8*i+5),16) ibytes))) (byteswap128 h3)))
         (word_pmul (word_bytereverse (bytes_to_int128 (SUB_LIST (16*(8*i+6),16) ibytes))) (byteswap128 h2)))
        (word_pmul (word_bytereverse (bytes_to_int128 (SUB_LIST (16*(8*i+7),16) ibytes))) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[GHASH_ACC_8BLOCK_EXTEND; MAP] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * i = 16 * (8*i+0)`] THEN
  MATCH_MP_TAC SPEC_TO_BYTEFORM_WB8_ACC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The GHASH reduction as a value equality.                                  *)
(*                                                                           *)
(* At the wire-in state (s289 in the loop body, s242 in the prepretail) the  *)
(* three Karatsuba accumulators are complete,                                *)
(*   PL = Q17 = Sum_k karatsuba_block_pl,                                    *)
(*   PH = Q19 = Sum_k karatsuba_block_ph,                                    *)
(*   PM = Q18 = Sum_k karatsuba_block_pm,                                    *)
(* with the reduction constant in Q16.  The simulation keeps them            *)
(* abbreviated (opaque), so after the reduction (in the loop body up to the  *)
(* eor3 at 0x9d0, s326) Q19 is the byteform on the left of                   *)
(* WBN_MACHINE_REDUCE_IS_PROP3_PACK below, over PL, PH and PM.  The lemma    *)
(* states that this byteform is                                              *)
(* polyval_reduce_prop3 (pack_corrected PL PH PM), with no outer             *)
(* word_reversefields: the form of BODY_Q19_CLOSE_ALGEBRA's right-hand side. *)
(*                                                                           *)
(* It is derived from the shared statement of this reduction,                *)
(* POLYVAL_REDUCE_G2 (aes_gcm_common.ml): pack_corrected (the zx/shl packing *)
(* the N-block GHASH Karatsuba layer is stated in) is karatsuba_join         *)
(* (PACK_CORRECTED_KARATSUBA_JOIN), so the right-hand side is                *)
(* polyval_reduce_g2 PL PH PM, and the byteform is the same xor of the same  *)
(* two pmuls up to rearrangement.  The statement keeps pack_corrected        *)
(* because KARA_ACC_PACK_HELPER, which packs the eight per-block triples in  *)
(* the Q19 close below, is stated with it.                                   *)
(* ------------------------------------------------------------------------- *)

let PACK_CORRECTED_KARATSUBA_JOIN = prove
 (`!pl ph pm:int128. pack_corrected pl ph pm = karatsuba_join pl ph pm`,
  REWRITE_TAC[pack_corrected; karatsuba_join] THEN BITBLAST_TAC);;

let POLYVAL_REDUCE_G2_KARATSUBA_JOIN = prove
 (`!p1 p2 p3:int128.
     polyval_reduce_g2 p1 p2 p3 = polyval_reduce_prop3 (karatsuba_join p1 p2 p3)`,
  REWRITE_TAC[karatsuba_join; POLYVAL_REDUCE_G2]);;

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
(* Block-algebra reconciliation facts.  They bridge the machine's            *)
(* accumulators at the wire-in state (Q17/Q19/Q18 = the separable sums       *)
(* PL/PH/PM, in raw word_reversefields / word_join / byteswap128-tower form) *)
(* to the kara_acc projection of an 8-quad list, so that                     *)
(* KARA_ACC_PACK_HELPER and KARATSUBA_BLOCK_PACKS_TO_PMUL_CLEAN pack them to *)
(* the sum of the word_pmul input_k h_k, the argument of                     *)
(* polyval_reduce_prop3 in BODY_Q19_CLOSE_ALGEBRA.  All are WORD_BLAST       *)
(* identities over free variables.                                           *)
(* ------------------------------------------------------------------------- *)

(* fact 1: the two byte-reversal spellings coincide (the machine uses        *)
(* word_reversefields 8, the spec and kara side word_bytereverse).           *)
let WRF8_IS_BYTEREVERSE = prove
 (`!x:int128. word_reversefields 8 x = word_bytereverse x`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* fact 2: karatsuba_mid is byteswap-invariant (it XORs the two 64-bit       *)
(* halves, and byteswap128 swaps them).  It lets the htable mid cell         *)
(* `karatsuba_mid h` satisfy the precondition `word_subword hk (0,64) =      *)
(* karatsuba_mid (byteswap128 h)` of KARATSUBA_BLOCK_PACKS_TO_PMUL_CLEAN.    *)
let KMID_BYTESWAP_INV = prove
 (`!h:int128. karatsuba_mid h = karatsuba_mid (byteswap128 h)`,
  GEN_TAC THEN REWRITE_TAC[karatsuba_mid; byteswap128] THEN CONV_TAC WORD_BLAST);;

(* fact 3 (block-0 SOFAR lane collapse): block 0's operand enters as a       *)
(* rot64'd word_join of the running accumulator SOFAR with the first         *)
(* ciphertext block.  The reduction takes the (64,64) / (0,64) sub-lane of   *)
(* the XOR of the two joins, which collapses to the plain (0,64) / (64,64)   *)
(* sub-lane of `word_xor S X`.                                               *)
let LANE_COLLAPSE = prove
 (`(!S X:int128. word_subword (word_xor (word_subword (word_join S S:256 word) (64,128):128 word)
                            (word_subword (word_join X X:256 word) (64,128):128 word)) (64,64):64 word
    = word_subword (word_xor S X) (0,64):64 word) /\
   (!S X:int128. word_subword (word_xor (word_subword (word_join S S:256 word) (64,128):128 word)
                            (word_subword (word_join X X:256 word) (64,128):128 word)) (0,64):64 word
    = word_subword (word_xor S X) (64,64):64 word)`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* fact 4 (the mid-input lanes of a pmull2/pmull pair): the machine computes *)
(* the PM mid products two blocks at a time (a pmull2, then a pmull, over    *)
(* the packed lanes of blocks A and B), and the (64,64) / (0,64) sub-lane of *)
(* the XOR of the hi-join and the lo-join recovers each block's (lo XOR hi)  *)
(* mid-input.  PM_LANE_HI' and PM_LANE_LO' (used by build_q19_reduce_clean   *)
(* and build_q19_reduce_clean_idx) spell it in the (0,64)^(64,64) lane order *)
(* that karatsuba_block_pm produces: WORD_RULE treats the first argument of  *)
(* word_pmul as atomic, so the lane XOR must match syntactically.            *)
let PM_LANE_HI' = prove
 (`!A B:int128.
    word_subword (word_xor (word_join (word_subword (A:int128) (64,64):64 word) (word_subword (B:int128) (64,64):64 word):128 word)
                           (word_join (word_subword A (0,64):64 word) (word_subword B (0,64):64 word):128 word)) (64,64):64 word
    = word_xor (word_subword A (0,64):64 word) (word_subword A (64,64):64 word)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let PM_LANE_LO' = prove
 (`!A B:int128.
    word_subword (word_xor (word_join (word_subword (A:int128) (64,64):64 word) (word_subword (B:int128) (64,64):64 word):128 word)
                           (word_join (word_subword A (0,64):64 word) (word_subword B (0,64):64 word):128 word)) (0,64):64 word
    = word_xor (word_subword B (0,64):64 word) (word_subword B (64,64):64 word)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* The block-0 and block-1 PM mid-inputs.  The first pmull2/pmull pair folds *)
(* in the running accumulator SOFAR, so block 0's operand enters as a        *)
(* rot64'd word_join of SOFAR with the first ciphertext block (not the plain *)
(* packed pair the later blocks use).  These two lane lemmas recover the     *)
(* block-0 (outer (64,64), over word_xor SOFAR cph0) and block-1 (outer      *)
(* (0,64), over cph1) mid-inputs, in karatsuba_block_pm's (0,64)^(64,64)     *)
(* lane order, by WORD_BLAST over free ss (= SOFAR), xx0 (= rev cph0) and    *)
(* xx1 (= rev cph1).  With PM_LANE_HI' and PM_LANE_LO' (the plain pairs      *)
(* {2,3}, {4,5}, {6,7}) they reduce all 8 machine PM mid-inputs to the kara  *)
(* form, so that PROJ_PM (in the builders below) closes.                     *)
let LANE_COLLAPSE_PM_A = prove
 (`!ss xx0 xx1:int128.
    word_subword
     (word_xor
      (word_join
       (word_subword (word_xor (word_subword (word_join (ss:int128) ss:256 word) (64,128):128 word)
                               (word_subword (word_join (xx0:int128) xx0:256 word) (64,128):128 word)) (0,64):64 word)
       (word_subword xx1 (64,64):64 word):128 word)
      (word_join
       (word_subword (word_xor (word_subword (word_join (ss:int128) ss:256 word) (64,128):128 word)
                               (word_subword (word_join (xx0:int128) xx0:256 word) (64,128):128 word)) (64,64):64 word)
       (word_subword xx1 (0,64):64 word):128 word)) (64,64):64 word
    = word_xor (word_subword (word_xor ss xx0) (0,64):64 word)
               (word_subword (word_xor ss xx0) (64,64):64 word)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let LANE_COLLAPSE_PM_B = prove
 (`!ss xx0 xx1:int128.
    word_subword
     (word_xor
      (word_join
       (word_subword (word_xor (word_subword (word_join (ss:int128) ss:256 word) (64,128):128 word)
                               (word_subword (word_join (xx0:int128) xx0:256 word) (64,128):128 word)) (0,64):64 word)
       (word_subword xx1 (64,64):64 word):128 word)
      (word_join
       (word_subword (word_xor (word_subword (word_join (ss:int128) ss:256 word) (64,128):128 word)
                               (word_subword (word_join (xx0:int128) xx0:256 word) (64,128):128 word)) (64,64):64 word)
       (word_subword xx1 (0,64):64 word):128 word)) (0,64):64 word
    = word_xor (word_subword xx1 (0,64):64 word) (word_subword xx1 (64,64):64 word)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

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

let build_q19_reduce_clean pl_t ph_t pm_t =
  build_q19_reduce_clean_idx `i:num` pl_t ph_t pm_t;;

(* Wire-in tactics.  The extract stashes pl/ph/pm at the wire-in state into  *)
(* refs, before the ABBREV that makes the reduce window small; the close     *)
(* (run at the Q19 postcondition conjunct) rebuilds the CLEAN theorem from   *)
(* those refs and accepts it after mapping its concrete byteform LHS back to *)
(* the goal's PL/PH/PM-abbreviated form and the 8*(i+1) = 8*i+8 index        *)
(* normalization the postcondition preparation applied.                      *)
let wbn_q19_pl = ref `T` and wbn_q19_ph = ref `T` and wbn_q19_pm = ref `T`;;
let WBN_Q19_EXTRACT_ABBREV_TAC (sN:string) : tactic =
  fun (asl,w) ->
    let st = mk_var(sN,`:armstate`) in
    let get_rhs q =
      let c = find (fun c -> match c with
        | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),qc),s)),_) when qc=q && s=st -> true
        | _ -> false) (map (concl o snd) asl) in
      rand c in
    wbn_q19_pl := get_rhs `Q17`;
    wbn_q19_ph := get_rhs `Q19`;
    wbn_q19_pm := get_rhs `Q18`;
    (ABBREV_TAC (mk_eq(`PL:int128`, !wbn_q19_pl)) THEN
     ABBREV_TAC (mk_eq(`PH:int128`, !wbn_q19_ph)) THEN
     ABBREV_TAC (mk_eq(`PM:int128`, !wbn_q19_pm))) (asl,w);;
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
(* wb_front_frame_tm writes only out_p, xi_p, ivec_p, the stack slot         *)
(* [sp+64,sp+80) and registers, which the nonoverlapping hypotheses keep     *)
(* apart from in_p, key_p and htbl_p.  The recomposition of Sec 12 uses it   *)
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
(* in_p, key_p and htbl_p; wbn_front_hyps_tm does not have those three       *)
(* disjointness conjuncts, so wbn_front_hyps_wide_tm adds them.              *)
(* WBN_FRONT_BUF_EXT is ENSURES_ADD_PRESERVED applied to WBN_FRONT_BUF       *)
(* (whose hypotheses the wide ones imply) and to the preservation            *)
(* obligation, which needs no simulation: the frame is unfolded and each     *)
(* read of R is pushed through the writes by WBN_PUSH_LHS_READ_TAC.          *)
(* ------------------------------------------------------------------------- *)

(* the wide >=17 hypotheses: wbn_front_hyps_tm plus the disjointness of out_p
   from in_p, key_p and htbl_p *)
let wbn_front_hyps_wide_tm =
  mk_conj(wbn_front_hyps_tm,
    `nonoverlapping (out_p:int64,16 * nblk) (in_p:int64,16 * nblk) /\
     nonoverlapping (out_p:int64,16 * nblk) (key_p:int64,240) /\
     nonoverlapping (out_p:int64,16 * nblk) (htbl_p:int64,192)`);;

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
     `htable_mem_dec h (htbl_p:int64) s`]);;

(* the EXT goal: wide hypotheses ==> ensures arm P (\s. Q0 s /\ R s) C *)
let wbn_front_ext_goal =
  let newQ = mk_abs(fst(dest_abs wbn_front_P_tm),
    mk_conj(rhs(concl(BETA_CONV(mk_comb(wbn_front_Q0_tm,fst(dest_abs wbn_front_P_tm))))),
            rhs(concl(BETA_CONV(mk_comb(wbn_front_R_tm,fst(dest_abs wbn_front_P_tm))))))) in
  let ens = list_mk_comb(`ensures arm`,[wbn_front_P_tm; newQ; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_wide_tm, ens));;

(* Push a read through the frame's write chain to `read c s` with
   COMPONENTS_READ_OVER_WRITE_ORTHOGONAL_CONV (common/components.ml), using the
   nonoverlapping assumptions, then close it by the precondition fact
   `read c s = value`.  The preservation legs of the _EXT theorems below apply
   it to each conjunct of R. *)
let WBN_PUSH_LHS_READ_TAC : tactic =
  W(fun (asl,w) ->
    let thl = map snd asl in
    let cxt = (NONOVERLAPPING_DRIVERS thl, FILTER_CANONIZE_ASSUMPTIONS thl) in
    CONV_TAC(LAND_CONV(COMPONENTS_READ_OVER_WRITE_ORTHOGONAL_CONV cxt))) THEN
  ASM_REWRITE_TAC[];;

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
    [`pc:num`;`ctr0:int128`;`in_p:int64`;`out_p:int64`;`xi_p:int64`;`ivec_p:int64`;
     `key_p:int64`;`htbl_p:int64`;`stackpointer:int64`;`nblk:num`;`ibytes:byte list`;
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
(* 9b. The raw counter Q30 in the loop invariant.                            *)
(*                                                                           *)
(* The first instruction of the body,                                        *)
(*   0x4bc  rev32 v5, v30                                                    *)
(* reads Q30, the running counter in the form the kernel keeps it, so the    *)
(* invariant must pin Q30, or Q5 stays symbolic in `read Q30 s0` and the     *)
(* body cannot close.  Every other vector register that the body reads       *)
(* before writing it is pinned by another conjunct.                          *)
(*                                                                           *)
(* gcm_ctr_raw w ctr0 is that form: each 32-bit lane of ctr0 byte-reversed,  *)
(* as rev32 reads it, with w added to the top lane.  The body computes rev32 *)
(* of v30, the AES input of block 8i+13, then add v30,v30,v31, which with    *)
(* v31 = word 2^96 advances the top lane to 8i+14, and so on for the 8       *)
(* blocks of the group.  So wbn_loop_invariant_raw has the conjunct          *)
(*   read Q30 s = gcm_ctr_raw (word (8 * i + 13)) ctr0                       *)
(* (inherited by wbn_loop_inv_core_raw).  WBN_FRONT_BUF's postcondition      *)
(* carries Q30 as a raw lane tower, which WBN_LOOP_INVARIANT_ENTRY_RAW       *)
(* rewrites to gcm_ctr_raw (word 13) ctr0 at i = 0 (gcm_ctr_raw_def, with    *)
(* the adds of 12 and 1 merged); the 8 adds of the body advance it from      *)
(* 8i+13 to 8(i+1)+13 = 8i+21.                                               *)
(*                                                                           *)
(* gcm_ctr_raw_def is defined with the front's term builders, and its lane   *)
(* lemmas (SUBW_RAW_*, GCM_CTR_RAW_INCR) are in Sec 2; this section has the  *)
(* two fold tactics.                                                         *)
(* ------------------------------------------------------------------------- *)

(* REV32_FOLD_TAC qd sn wtm: after a step rev32 vd,v30 that reads
   Q30 = gcm_ctr_raw wtm ctr0, rewrite the stepper's lane tower in
   `read qd sn = <tower>` (wherever it occurs in the assumptions) to
   gcm_ctr_add wtm ctr0, the AES input block for counter wtm.  The fold
   equation is proved on the fly from the tower in the assumption, for a
   fresh w:32 word in place of wtm: both sides are unfolded to lanes
   (gcm_ctr_raw_def, GCM_CTR_ADD_LANES), the symbolic top-lane sum is
   generalized to a fresh variable, and WORD_BLAST proves the rest, so it
   never meets the symbolic addend. *)
let REV32_FOLD_TAC (qd:string) (sn:string) (wtm:term) : tactic =
  fun (asl,gl) ->
    let tower = tryfind (fun (_,th) -> match concl th with
      | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),st)),r)
          when string_of_term c = qd && (try fst(dest_var st)=sn with _ -> false) -> r
      | _ -> fail()) asl in
    (* the fold for a fresh w:32 word, then w := wtm *)
    let tower_gen = subst [`w:32 word`, wtm] tower in
    let fold_thm = prove(mk_eq(tower_gen, `gcm_ctr_add w ctr0`),
      REWRITE_TAC[gcm_ctr_raw_def] THEN
      GEN_REWRITE_TAC RAND_CONV [GCM_CTR_ADD_LANES] THEN
      W(fun (_,gw) ->
         let atom = find_term (fun t -> match t with
           | Comb(Comb(Const("word_add",_),_),Var("w",_)) -> true | _ -> false) gw in
         SPEC_TAC(atom, `aa:32 word`)) THEN
      GEN_TAC THEN CONV_TAC WORD_BLAST) in
    let fold_spec = INST [wtm,`w:32 word`] fold_thm in
    RULE_ASSUM_TAC(REWRITE_RULE[fold_spec]) (asl,gl);;

(* CTR_RAW_INCR_FOLD_TAC qd sn wtm: the increment counterpart of
   REV32_FOLD_TAC.  After an `add v30,v30,v31` step, the assumption
     read qd sn = <single-add tower over gcm_ctr_raw wtm ctr0>
   (top lane word_add (word_subword (gcm_ctr_raw wtm ctr0) (96,32)) (word 1),
   the other lanes + 0) is rewritten by GCM_CTR_RAW_INCR at w := wtm to
     read qd sn = gcm_ctr_raw (word_add wtm (word 1)) ctr0.
   Fold once per add, before the next add nests the increments, so that only
   the single-add left-hand side of GCM_CTR_RAW_INCR ever has to match. *)
let CTR_RAW_INCR_FOLD_TAC (qd:string) (sn:string) (wtm:term) : tactic =
  let incr_spec = INST [wtm,`w:32 word`] GCM_CTR_RAW_INCR in
  RULE_ASSUM_TAC(fun th ->
    match concl th with
    | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),st)),_)
        when string_of_term c = qd && (try fst(dest_var st)=sn with _ -> false) ->
        REWRITE_RULE[incr_spec] th
    | _ -> th);;

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
    [`pc:num`;`ctr0:int128`;`in_p:int64`;`out_p:int64`;`xi_p:int64`;`ivec_p:int64`;
     `key_p:int64`;`htbl_p:int64`;`stackpointer:int64`;`nblk:num`;`ibytes:byte list`;
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

(* The next group's raw ciphertext blocks 8(i+1) .. 8(i+1)+7, which the
   body's ldp's load into Q8..Q15, are derived at each load from the
   input-buffer loop constant
     read (memory :> bytes (in_p,16 * nblk)) s = num_of_bytelist ibytes,
   which the body preserves (in_p is only read, and out_p is disjoint from
   it).  From the step-case bound i < (nblk-9) DIV 8, WBN_RAWCT_BOUND gives
     8(i+1)+m < nblk  for m < 8,
   and WBN_RAWCT_READ, by INPUT_BYTES_TO_BYTE128_LANES, the block reads
     read (memory :> bytes128 (in_p + 16*(8(i+1)+m))) s =
     bytes_to_int128 (SUB_LIST (16*(8(i+1)+m),16) ibytes),
   the invariant's values of Q8..Q15 at i+1. *)
let WBN_RAWCT_BOUND = prove
 (`i < (nblk - 9) DIV 8 /\ 9 <= nblk ==> !m. m < 8 ==> 8 * (i+1) + m < nblk`,
  STRIP_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`nblk - 9`; `8`] DIVISION) THEN ASM_ARITH_TAC);;

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
   [ASM_REWRITE_TAC[LE_REFL] THEN
    SUBGOAL_THEN `SUB_LIST (0, 16 * nblk) (ibytes:byte list) = ibytes` SUBST1_TAC THENL
     [MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(SPEC_ALL WBN_RAWCT_BOUND) THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 10a. Loop-body simulation machinery.                                      *)
(*                                                                           *)
(* The loop body 0x4bc..0xa08 (340 instructions) is one software-pipelined   *)
(* 8-block group: 8 AES-256 keystream towers, the GHASH fold of the 8        *)
(* ciphertext blocks of the previous group, the counter advancing 8i+13 ->   *)
(* 8i+21 = 8(i+1)+13, 4 stp stores of 8 plaintext blocks, the ldp loads of   *)
(* the next group and the signed b.lt back-edge.  WBN_MAIN_LOOP_raw          *)
(* simulates it, s0..s340, as follows.                                       *)
(* - Counter folds: after each rev32 vd,v30, REV32_FOLD_TAC "Qd" "sN"        *)
(*   `word (8*i+c)`; after each add v30,v30,v31, CTR_INCR_NORM_TAC "sN" c,   *)
(*   which folds it and normalizes the index to word (8*i+(c+1)).            *)
(* - Steps 1..13, the counter setup: ARM_STEPS_TAC, GCM_SIMD_SIMPLIFY_TAC.   *)
(* - Steps 14..289, AES and GHASH: ARM_STEPS_FOLD_KEEPDATA_TAC, which keeps  *)
(*   the latest read of each of Q0..Q19.                                     *)
(* - Steps 290..340, the GHASH reduction over the abbreviated accumulators,  *)
(*   the stores and the back-edge: ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC.       *)
(* - The back-edge b.lt at 0xa08: the NF/VF facts of the cmp x0,x5 come from *)
(*   WB_PTRCMP_FLAGS (a = 128*(i+2), d = 128*((nblk-1) DIV 8)) as separate   *)
(*   theorems rewritten into the assumptions (adding them to the goal with   *)
(*   MP_TAC breaks the stp step that follows).  The PC lands at              *)
(*     if 128*(i+2) < 128*((nblk-1) DIV 8) then 0x4bc else 0xa0c,            *)
(*   which WBN_PC_BRIDGE turns into the test i+1 < (nblk-9) DIV 8.           *)
(* ------------------------------------------------------------------------- *)

(* CTR_INCR_NORM_TAC sn c: fold the add v30 at state sn (CTR_RAW_INCR_FOLD_TAC
   on Q30), then normalize the counter index
     word_add (word (8*i+c)) (word 1)  to  word (8*i+(c+1)) *)
let CTR_INCR_NORM_TAC (sn:string) (c:int) : tactic =
  let cur = mk_comb(`word:num->32 word`,
    mk_binop `(+):num->num->num` `8*i` (mk_small_numeral c)) in
  let nrm = WORD_RULE (mk_eq(
    mk_binop `word_add:32 word->32 word->32 word` cur `word 1:32 word`,
    mk_comb(`word:num->32 word`,
      mk_binop `(+):num->num->num` `8*i` (mk_small_numeral (c+1))))) in
  CTR_RAW_INCR_FOLD_TAC "Q30" sn cur THEN RULE_ASSUM_TAC(REWRITE_RULE[nrm]);;

(* DISCARD_STALE_Q19_TAC: keep only the latest `read Q19 sN` fact (the GHASH
   accumulator, whose values at older states are dead); the Q19 analogue of
   DISCARD_STALE_Q18_TAC. *)
let state_num_of_q19_fact th =
  try let c = concl th in if not(is_eq c) then None else
    (match lhs c with
       Comb(Comb(Const("read",_),Const("Q19",_)),Var(sn,_))
         when String.length sn>1 && sn.[0]='s' ->
           Some(int_of_string(String.sub sn 1 (String.length sn-1)))
     | _ -> None) with _ -> None;;
let DISCARD_STALE_Q19_TAC : tactic = fun (asl,w) ->
  let nums = List.filter_map (fun (_,th) -> state_num_of_q19_fact th) asl in
  match nums with [] | [_] -> ALL_TAC (asl,w)
  | _ -> let mx = List.fold_left max 0 nums in
         DISCARD_ASSUMPTIONS_TAC (fun th ->
           (match state_num_of_q19_fact th with Some k -> k<mx | None -> false)) (asl,w);;

(* DISCARD_STALE_QREG_TAC qn: keep only the latest `read qn sN` fact of
   register qn.  DISCARD_STALE_DATA_TAC below applies it to each of Q0..Q19 for
   the KEEPDATA steppers. *)
let state_num_of_qreg qn th =
  try let c = concl th in if not(is_eq c) then None else
    (match lhs c with
       Comb(Comb(Const("read",_),Const(n,_)),Var(sn,_))
         when n=qn && String.length sn>1 && sn.[0]='s' ->
           Some(int_of_string(String.sub sn 1 (String.length sn-1)))
     | _ -> None) with _ -> None;;
let DISCARD_STALE_QREG_TAC qn : tactic = fun (asl,w) ->
  let nums = List.filter_map (fun (_,th) -> state_num_of_qreg qn th) asl in
  match nums with [] | [_] -> ALL_TAC (asl,w)
  | _ -> let mx = List.fold_left max 0 nums in
         DISCARD_ASSUMPTIONS_TAC (fun th ->
           (match state_num_of_qreg qn th with Some k -> k<mx | None -> false)) (asl,w);;
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

(* ------------------------------------------------------------------------- *)
(* 10c. Loop-body close machinery.                                           *)
(*                                                                           *)
(* The steppers and resolvers of the body simulation.  The KEEPDATA steppers *)
(* keep the latest read of each of Q0..Q19, the keystreams in Q0..Q7         *)
(* included, which the store readbacks need.  The ldp's of the next group    *)
(* are resolved at load by RESOLVE_LDP2_TAC: an ldp leaves                   *)
(*   read Qk sN = read (memory :> bytes128 ADDR) s(N-1),                     *)
(* a memory read at the load-input state s(N-1), so the raw !m lemma has to  *)
(* be matched at s(N-1), not at sN.  RESOLVE_QREG_C matches it at the state  *)
(* of the register read's own memory read, and uses PURE_ONCE_REWRITE: plain *)
(* REWRITE would reduce 8*(i+1)+0 to 8*(i+1) and break the m = 0 ACCEPT.     *)
(* ------------------------------------------------------------------------- *)

(* The KEEPDATA discard: keep every fact that reads one of Q0..Q19
   (DISCARD_STALE_DATA_TAC then keeps only the latest read of each) and every
   fact that mentions no state but the current one; discard every other
   old-state fact. *)
let wbn_datawords_0_19 =
  ["Q0";"Q1";"Q2";"Q3";"Q4";"Q5";"Q6";"Q7";"Q8";"Q9";
   "Q10";"Q11";"Q12";"Q13";"Q14";"Q15";"Q16";"Q17";"Q18";"Q19"];;
let DISCARD_OLDSTATE_KEEPDATA_TAC s =
  let v = mk_var(s,`:armstate`) in
  let rec unbound_statevars_of_read bound tm = match tm with
      Comb(Comb(Const("read",_),_),st) -> if mem st bound then [] else [st]
    | Comb(a,b) -> union (unbound_statevars_of_read bound a) (unbound_statevars_of_read bound b)
    | Abs(vv,t) -> unbound_statevars_of_read (vv::bound) t | _ -> [] in
  let rec mentions_data t = match t with
      Comb(Comb(Const("read",_),cmp),_) ->
        (match cmp with Const(n,_) -> List.mem n wbn_datawords_0_19 | _ -> false)
    | Comb(a,b) -> mentions_data a || mentions_data b | Abs(_,t2) -> mentions_data t2 | _ -> false in
  DISCARD_ASSUMPTIONS_TAC(fun thm ->
    if mentions_data (concl thm) then false else
    let us = unbound_statevars_of_read [] (concl thm) in
    if us = [] || us = [v] then false else true);;
let DISCARD_STALE_DATA_TAC = MAP_EVERY DISCARD_STALE_QREG_TAC wbn_datawords_0_19;;
(* The KEEPDATA steppers normalize each step with one pass of the
   GCM_SIMD_SIMPLIFY_CORE_TAC rewrites, not with the double pass
   GCM_SIMD_SIMPLIFY_TAC.  The second pass only reaches a REV64 fixpoint that
   one pass can miss on a few steps, and the KEEPDATA windows of the loop body
   and of the prepretail, the only users of these steppers, do not need it.
   (The fronts, ARM_VSTEPS_FOLD_TAC and ARM_STEPS_FOLD_DISCARD_TAC use the
   double pass; the KEEPGH, Q18-latest and KEEPGHALL steppers also use one.)

   The pass is also Q-scoped and memoized, like those of gcm_simd_kgh_tbl and
   gcm_simd_fixpt_tbl: it is applied only to `read Qn s = ...` assumptions, the
   ones its rules are for, and skips an assumption whose conclusion
   gcm_simd_kd_tbl records as already a fixpoint.  The pass is a function of
   the conclusion alone, so skipping a recorded fixpoint changes nothing.
   CLEAR_KEEPDATA_MEMO_TAC empties the table at the start of each of the two
   simulations, so that each proof is self-contained. *)
let gcm_simd_kd_tbl : (term,unit) Hashtbl.t = Hashtbl.create 8192;;
let CLEAR_KEEPDATA_MEMO_TAC : tactic =
  fun (asl,w) -> Hashtbl.clear gcm_simd_kd_tbl; ALL_TAC (asl,w);;
let GCM_SIMD_SIMPLIFY_KD_TAC = GCM_SIMD_SIMPLIFY_MEMO_TAC gcm_simd_kd_tbl;;
let ARM_STEPS_FOLD_KEEPDATA_TAC exec snums =
  MAP_EVERY (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN GCM_SIMD_SIMPLIFY_KD_TAC THEN
              DISCARD_STALE_DATA_TAC THEN DISCARD_OLDSTATE_KEEPDATA_TAC s THEN CLARIFY_TAC)
    (statenames "s" snums);;
(* The variant without the SIMD normalizer, for the reduction and the store
   windows: normalizing the pmulls by the [sp+64] reduction constant there, or
   the eor3 keystream towers the stores keep, blows the terms up, so these
   steps are taken symbolically. *)
let ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC exec snums =
  MAP_EVERY (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN
              DISCARD_STALE_DATA_TAC THEN DISCARD_OLDSTATE_KEEPDATA_TAC s THEN CLARIFY_TAC)
    (statenames "s" snums);;
(* DISCARD_QREGS_TAC qns: drop every `read Qn sN` fact of the listed registers,
   at any state; used before the final split of the body postcondition to drop
   the GHASH and scratch registers no conjunct needs. *)
let DISCARD_QREGS_TAC qns : tactic =
  DISCARD_ASSUMPTIONS_TAC(fun th -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const(n,_)),Var(_,_))),_) -> List.mem n qns
    | _ -> false);;

(* RESOLVE_QREG_C qreg scur m: resolve the raw read an ldp leaves,
     read qreg scur = read (memory :> bytes128 ADDR) sload,
   against the raw lemma at sload (the load-input state); PURE_ONCE_REWRITE
   keeps the m = 0 index 8*(i+1)+0 unreduced for the ACCEPT *)
let RESOLVE_QREG_C (qreg:string) (scur:string) (m:int) : tactic =
  fun (asl,w) ->
    let mnum = mk_small_numeral m in
    let th,addr,sload = tryfind (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const(n,_)),Var(sn,_))),
             Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),Const("memory",_)),
               Comb(Const("bytes128",_),addr))),Var(sl,_)))
          when n=qreg && sn=scur -> (th,addr,sl)
      | _ -> fail()) asl in
    let raw = tryfind (fun (_,t) -> match concl t with
        Comb(Const("!",_),Abs(Var("m",_),Comb(Comb(Const("==>",_),_),
          Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),Var(sl,_))),
               Comb(Const("bytes_to_int128",_),_))))) when sl=sload -> t
      | _ -> fail()) asl in
    let canon = vsubst[mnum,`m:num`] `word_add in_p (word (16 * (8*(i+1)+m))):int64` in
    let addr_eq = WORD_RULE (mk_eq(addr,canon)) in
    let raw_inst = MATCH_MP raw (ARITH_RULE(mk_comb(mk_comb(`(<):num->num->bool`,mnum),`8`))) in
    let target = mk_eq((parse_term (Printf.sprintf "read %s %s :int128" qreg scur)),
      vsubst[mnum,`m:num`] `bytes_to_int128 (SUB_LIST (16 * (8*(i+1)+m), 16) ibytes)`) in
    (SUBGOAL_THEN target ASSUME_TAC THENL
      [GEN_REWRITE_TAC LAND_CONV [th] THEN PURE_ONCE_REWRITE_TAC[addr_eq] THEN ACCEPT_TAC raw_inst;
       ALL_TAC]) (asl,w);;

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

(* the back-edge arithmetic: the b.lt compares 128 * (i + 2) with
   128 * ((nblk - 1) DIV 8), i.e. tests i + 1 < (nblk - 9) DIV 8 *)
let WBN_DIV_SHIFT = prove
 (`9 <= nblk ==> (nblk - 1) DIV 8 = (nblk - 9) DIV 8 + 1`,
  STRIP_TAC THEN
  SUBGOAL_THEN `nblk - 1 = (nblk - 9) + 1 * 8` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DIV_ADD_MOD] THEN
  SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN ARITH_TAC);;

let WBN_PC_BRIDGE = prove
 (`9 <= nblk
   ==> ((128 * (i + 2) < 128 * (nblk - 1) DIV 8) <=> (i + 1 < (nblk - 9) DIV 8))`,
  DISCH_TAC THEN ASM_SIMP_TAC[WBN_DIV_SHIFT] THEN ARITH_TAC);;

(* premises of WB_PTRCMP_FLAGS at the back-edge, X0 = in_p+128*(i+2) (a)
   and X5 = 128*((nblk-1) DIV 8)+in_p (d): val in_p plus either offset is
   below 2^63, by val in_p + 16*nblk < 2^63 *)
let WBN_PTRCMP_PREMS = prove
 (`val (in_p:int64) + 16 * nblk < 2 EXP 63 /\ i < (nblk - 9) DIV 8
   ==> val (in_p:int64) + 128 * (i + 2) < 2 EXP 63 /\
       val (in_p:int64) + 128 * (nblk - 1) DIV 8 < 2 EXP 63`,
  STRIP_TAC THEN
  MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN
  MP_TAC(SPECL [`nblk - 9`; `8`] DIVISION) THEN ASM_ARITH_TAC);;

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
         X10 = sp+64, X11 = key_p, X3 = xi_p, X6 = htbl_p, X16 = ivec_p,
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
(*   X3 = xi_p, X6 = htbl_p, X16 = ivec_p, X15 = 2^32, Q31 = 2^96,           *)
(*   SP = stackpointer, [sp+64] = 0xC2..., the round keys k0..k14, the       *)
(*   htable, the input buffer and the stores j < 8*(k+1)                     *)
(* ========================================================================= *)

(* The s313 seam state, built like wb_front_postcond from the final state of
   the simulation.  Q19 and its staging Q16 are stated at a fresh xi', as the
   substitution source for wbn_prepretail_post below: with xi' unconstrained
   this is not a true postcondition (word_bytereverse is a bijection and the
   model is deterministic).  The counter registers are
   Q0..Q7 = aes13 (gcm_ctr_add (word (8*k+8+i)) ctr0) k0..k13, i = 0..7.  It
   leaves out the xi_p, ivec_p, [sp+72] and in_p block 0 cells, which the tail
   does not read: the tail (0xef0..0x11c8, and the exact-8 drain
   0x11e4..0x1360) only stores ivec_p (str q30,[x16] at 0x1160, or 0x1330 in
   the drain) and xi_p (st1 v19,[x3] at 0x11c8), and its only stack load is the
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
    `read X3 s = xi_p`;
    `read X6 s = htbl_p`;
    `read (memory :> bytes (in_p,16 * nblk)) s = num_of_bytelist ibytes`] @
   wbp_key_reads @ wbp_htable_reads @ wbp_ctx `xi':int128` @
   [wbp_rd `Q5` (wbp_aes13 (ctr 13));
    wbp_rd `Q2` (wbp_aes13 (ctr 10));
    wbp_rd `Q4` (wbp_aes13 (ctr 12));
    wbp_rd `Q3` (wbp_aes13 (ctr 11));
    `read X5 s = word_sub (word_add in_p (word (16 * nblk)))
                          (word_add in_p (word (128 * ((nblk - 9) DIV 8 + 1))))`;
    `read X0 s = word_add (word_add in_p (word (128 * ((nblk - 9) DIV 8 + 1)))) (word 16)`]);;

(* The caught-up GHASH accumulator: the loop invariant's Q19 at i := k + 1, the
   fold over all 8 * (k + 1) processed blocks.  This is the value of Q19 at the
   seam: the loop exits with the GHASH stream one 8-block group behind, and the
   prepretail folds that group in.  It is a function of the pinned inputs
   (xi, h, ibytes, nblk), not a fresh variable. *)
let wbn_caught_up = `ghash_polyval_acc (byteswap128 (h:int128)) (word_bytereverse (xi:int128))
    (MAP word_bytereverse
    (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) (ibytes:byte list)))
                 (8 * (((nblk:num) - 9) DIV 8 + 1))))`;;

(* The seam post: the raw post with its fresh word_bytereverse xi', which
   occurs only in the Q19 and Q16 conjuncts, replaced by the caught-up
   accumulator, so that Q19 = wbn_caught_up (the invariant's shape at
   i := k + 1) and Q16 is its staging
   word_subword (word_join wbn_caught_up wbn_caught_up) (64,128).  xi' is gone,
   so the post is over the variables of wb_front_vars only. *)
let wbn_prepretail_post =
  subst [wbn_caught_up, `word_bytereverse (xi':int128)`] wbn_prepretail_post_raw;;

(* The first tail block's index is in range: 8 * k + 8 < nblk for
   k = (nblk - 9) DIV 8 and 9 <= nblk, the index bound that
   WBN_PREPRETAIL_EXT2_UNIFIED passes to WBN_PREPRETAIL_EXT2_TAC. *)
let WBN_Q9_INDEX_LT_9 = prove
 (`!nblk. 9 <= nblk /\ 128 * nblk < 2 EXP 64 ==> 8 * ((nblk - 9) DIV 8) + 8 < nblk`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL[`nblk - 9`;`8`] DIVISION) THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `k = (nblk - 9) DIV 8` THEN ASM_ARITH_TAC);;

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
(* by INPUT_BYTES_TO_BYTE128_LANES at lane 8*(k+1), from 8*(k+1) < nblk and  *)
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
    INPUT_BYTES_TO_BYTE128_LANES) THEN
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

(* ------------------------------------------------------------------------- *)
(* The tail leg: from the seam to the core exit (WBN_PREP_TO_END).           *)
(*                                                                           *)
(* The tail back-legs WB_TAIL_GEN2_1..8 of the <=8-block chain start at the  *)
(* seam PC pc+3824 and run to the core exit pc+4556, closing the r-block     *)
(* GHASH with GMULT_FULL_CORRECT_BA (r = 1) or GMULT2..8_FULL_CORRECT_BA.    *)
(* They are proved once, before prove_band (which uses them too), where      *)
(* their goal builders wbn_dissect_band, wbn_tail_drop_lhs5,                 *)
(* wbn_weak_q_at5_return and wbn_tail_backleg_goal5_return are defined as    *)
(* well.  Here the seam post wbn_prepretail_post_ext2 feeds them at shifted  *)
(* indices (shift_vals r): precondition weakening, no re-simulation.         *)
(*                                                                           *)
(* The back-legs keep X9 generic (return_value).  The seam has               *)
(* X1 = word (128 * nblk) and X9 = word (16 * nblk), where a tail fixed to r *)
(* blocks would have word (128 * r) and word (16 * r), which differ for      *)
(* nblk >= 17.  The tail (0xef0..0x11c8, and the exact-8 drain               *)
(* 0x11e4..0x1360) reads neither register, so the back-leg contract drops X1 *)
(* and keeps X9 as return_value: the shifted tail instantiates it to         *)
(* word (16 * nblk), a fixed band to word (16 * r).                          *)
(* ------------------------------------------------------------------------- *)

(* num_of_bytelist = num_of_wordlist on byte lists (used by
   WBN_INPUT_SLICE_GEN). *)
let NUM_OF_BYTELIST_EQ_WORDLIST = prove
 (`!l:byte list. num_of_bytelist l = num_of_wordlist l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[num_of_bytelist; num_of_wordlist; DIMINDEX_8] THEN ARITH_TAC);;

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
(* tail's own hypotheses (nonoverlapping over the shifted out_p, xi_p and    *)
(* ivec_p regions) need three disjointness clauses the wide hypotheses do    *)
(* not carry:                                                                *)
(*   nonoverlapping (out_p,16*nblk) (xi_p,16)                                *)
(*   nonoverlapping (out_p,16*nblk) (ivec_p,16)                              *)
(*   nonoverlapping (xi_p,16)       (ivec_p,16)                              *)
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
    `xi_p:int64`; `ivec_p:int64`;
    `word_add in_p (word (128 * ((nblk - 9) DIV 8 + 1))):int64`;
    `key_p:int64`; `htbl_p:int64`;
    slice; xi_shifted;
    `gcm_ctr_add (word (8 * ((nblk - 9) DIV 8 + 1))) ctr0:int128`;
    `k0:int128`;`k1:int128`;`k2:int128`;`k3:int128`;`k4:int128`;`k5:int128`;`k6:int128`;`k7:int128`;
    `k8:int128`;`k9:int128`;`k10:int128`;`k11:int128`;`k12:int128`;`k13:int128`;`k14:int128`;`h:int128`;
    `word (16 * nblk):int64`];;

(* the three side conditions of the tail legs, at the whole-buffer length *)
let wbn_prep_to_end_extra_clauses =
  [`nonoverlapping (out_p:int64,16 * nblk) (xi_p:int64,16)`;
   `nonoverlapping (out_p:int64,16 * nblk) (ivec_p:int64,16)`;
   `nonoverlapping (xi_p:int64,16) (ivec_p:int64,16)`];;

(* ------------------------------------------------------------------------- *)
(* The tag fold and the output forall.                                       *)
(*                                                                           *)
(* The seam feed (INNER_TAIL_FEED_TAC with WB_TAIL_GEN2_r) gives the shifted *)
(* band's post:                                                              *)
(*   - PC = pc+4556, the core exit;                                          *)
(*   - the last r output stores, at out_p + 128*(k+1) + 16*i (i < r);        *)
(*   - the tag at xi_p: the caught-up accumulator continued over the r new   *)
(*     blocks.                                                               *)
(* It does not have the first 8*(k+1) output stores, which the seam post     *)
(* carries as its output forall.  The full-nblk contract needs               *)
(*   (a) that forall carried through the r-block tail, whose frame writes    *)
(*       only bytes (out_p+128(k+1),16*r), disjoint from the first           *)
(*       128*(k+1) bytes (ENSURES_ADD_PRESERVED), and                        *)
(*   (b) the tag fold, caught_up ++ [r new blocks] = list_of_seq cph nblk,   *)
(*       by GHASH_ACC_APPEND.                                                *)
(* The lemmas below are the list and tag algebra for (b).                    *)
(* ------------------------------------------------------------------------- *)

(* list_of_seq splits at any point into a prefix + a shifted suffix. *)
let LIST_OF_SEQ_ADD = prove
 (`!m (f:num->A) n. list_of_seq f (m + n) =
        APPEND (list_of_seq f m) (list_of_seq (\i. f (m + i)) n)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; LIST_OF_SEQ; APPEND; ETA_AX];
    REWRITE_TAC[ADD_CLAUSES; LIST_OF_SEQ; APPEND] THEN
    AP_TERM_TAC THEN ASM_REWRITE_TAC[o_DEF]]);;

(* LIST_OF_SEQ_CLAUSES (common/misc.ml) covers n = 0..4 only; the r-block tag
   fold needs the expansion up to n = 8.  Each is proved from the SUC recursion
   (num_CONV down to a count LIST_OF_SEQ_CLAUSES covers, then APPEND). *)
let LIST_OF_SEQ_CLAUSES_5_8 =
  let expand_los n =
    let suc_convs = map (fun k -> num_CONV (mk_small_numeral k)) (rev (5--n)) in
    prove(mk_forall(`f:num->A`,
       mk_eq(list_mk_comb(`list_of_seq:(num->A)->num->(A)list`,[`f:num->A`; mk_small_numeral n]),
             mk_list(map (fun i -> mk_comb(`f:num->A`, mk_small_numeral i)) (0--(n-1)), `:A`))),
      GEN_TAC THEN
      GEN_REWRITE_TAC TOP_DEPTH_CONV suc_convs THEN
      REWRITE_TAC[list_of_seq] THEN
      CONV_TAC(DEPTH_CONV NUM_SUC_CONV) THEN
      REWRITE_TAC[LIST_OF_SEQ_CLAUSES] THEN REWRITE_TAC[APPEND]) in
  end_itlist CONJ (map expand_los [5;6;7;8]);;

(* fold one gcm_ctr_inc into the running gcm_ctr_add offset (for the
   gcm_ctr_inc^i counters of the tail stores in WBN_PREP_TO_END_FULL_r) *)
let GCM_CTR_INC_FOLD = prove
 (`!w x. gcm_ctr_inc (gcm_ctr_add w x) = gcm_ctr_add (word_add w (word 1)) x`,
  REWRITE_TAC[GSYM GCM_CTR_ADD_1; GCM_CTR_ADD_COMPOSE]);;

(* nesting: the shifted band's i-th cph block = the global (8*(k+1)+i)-th. *)
let WBN_SUBLIST_SHIFT = prove
 (`!(ibytes:byte list) k i r. i < r
   ==> SUB_LIST (16 * i,16) (SUB_LIST (128 * (k + 1),16 * r) ibytes) =
       SUB_LIST (16 * (8 * (k + 1) + i),16) ibytes`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUB_LIST_MIN_GENERAL] THEN
  SUBGOAL_THEN `MIN 16 (16 * r - 16 * i) = 16` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `128 * (k + 1) + 16 * i = 16 * (8 * (k + 1) + i)` SUBST1_TAC THENL
   [ARITH_TAC; REFL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* WBN_PREP_TO_END_FULL_r: the seam post fed to the shifted tail, with the   *)
(* full-nblk contract as its post (not the r-block band_post).  The post is  *)
(* wbn_end_post: PC = pc+4556, X9 = word (16 * nblk), the output forall over *)
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
  let tag = `read (memory :> bytes128 xi_p) s =
    word_bytereverse (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      (MAP word_bytereverse
        (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes)) nblk)))` in
  (* ivec: the whole-buffer counter write-back, spine form
     gcm_ctr_inc_iter nblk ctr0.  FULL_r reconciles the shifted band's
     gcm_ctr_inc_iter r (gcm_ctr_add (word 8(q+1)) ctr0) to this via
     GCM_CTR_INC_ITER_AS_ADD + GCM_CTR_ADD_COMPOSE (8(q+1)+r = nblk). *)
  let ivec = `read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter nblk ctr0` in
  mk_abs(`s:armstate`,
    list_mk_conj [`read PC s = word (pc + 4556)`;
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

(* ------------------------------------------------------------------------- *)
(* WBN_PREP_TO_END_FULL_r for r = 2..8.                                      *)
(*                                                                           *)
(* They have the skeleton of WBN_PREP_TO_END_FULL_1; the parts that depend   *)
(* on r are OCaml int -> tactic closures, driven by                          *)
(* WBN_PREP_TO_END_FULL_r_TAC.                                               *)
(*                                                                           *)
(* The per-block algebra: for output block j = 8*(q+1)+i (0 <= i < r) the    *)
(* value the seam's forall states equals the r-block band's store.           *)
(* wbn_block_bridge_goal and wbn_block_bridge_tac prove that identity on its *)
(* own, goal form word_xor (word_xor cph aes13) k14 = store form             *)
(* word_xor cph (aes256_encrypt ...), reconciling                            *)
(*   - the counter, by GCM_CTR_INC_FOLD:                                     *)
(*       gcm_ctr_inc_iter (8(q+1)+i) = gcm_ctr_add (word (8(q+1)+i))         *)
(*         = gcm_ctr_inc^i (gcm_ctr_add (word (8(q+1))));                    *)
(*   - the input slice, by WBN_SUBLIST_SHIFT:                                *)
(*       SUB_LIST (16*(8(q+1)+i),16) ibytes =                                *)
(*         SUB_LIST (16*i,16) (SUB_LIST (128(q+1),16*r) ibytes);             *)
(*   - the cipher: GSYM AES256_XOR_ENCRYPT_RECONSTRUCT, then WORD_RULE       *)
(*     for the XOR reassociation.                                            *)
(* wbn_block_close_tac then reduces 16*i to a numeral (otherwise the goal's  *)
(* SUB_LIST (16*i,..) and word (16*i) do not match the store's numerals) and *)
(* reconciles the store address (flat for i = 0, nested for i >= 1).         *)
(* wbn_tag_fold_tac folds the explicit r-element tag list to list_of_seq by  *)
(* LIST_OF_SEQ_ADD and GHASH_ACC_APPEND, closing each element by             *)
(* WBN_SUBLIST_SHIFT.                                                        *)
(* ------------------------------------------------------------------------- *)

(* the goal-side and store-side counter for output block i (0<=i<r). *)
let wbn_full_goal_ctr i =
  subst[mk_small_numeral i,`i_:num`]
    `gcm_ctr_add (word (8 * (q + 1) + i_)) ctr0 :int128`;;
let wbn_full_store_ctr i =
  funpow i (fun t -> mk_comb(`gcm_ctr_inc:int128->int128`, t))
    `gcm_ctr_add (word (8 * (q + 1))) ctr0 :int128`;;
(* the goal-side and store-side output addresses for block i. *)
let wbn_full_goal_addr i =
  subst[mk_small_numeral i,`i_:num`]
    `word_add out_p (word (16 * (8 * (q + 1) + i_))):int64`;;
let wbn_full_store_addr i =
  if i = 0 then `word_add out_p (word (128 * (q + 1))):int64`
  else mk_comb(mk_comb(`word_add:int64->int64->int64`,
                       `word_add out_p (word (128 * (q + 1))):int64`),
               mk_comb(`word:num->int64`, mk_small_numeral(16 * i)));;

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

(* derive a banded leg (the wide >=17 band or the 9..16 band) from the
   union-band FREE_r: MATCH_MP_TAC on the same ensures term, ASM_REWRITE_TAC
   for the shared hypotheses, ASM_ARITH_TAC for the band.
   WBN_PREPRETAIL_EXT2_916 below is derived in the same way. *)
let wbn_prep_to_end_full_derive_tac free_thm =
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC free_thm THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;;

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
(*   tail        pc+3824 -> pc+4556             WBN_PREP_TO_END_916          *)
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

(* ------------------------------------------------------------------------- *)
(* Tag-side bridge lemmas (no simulation, symbolic nblk).                    *)
(*                                                                           *)
(* They turn the tag conjunct of wbn_end_post into the NIST nist_ghash form  *)
(* at a symbolic block count (LIST_OF_SEQ_NIST_INPUT of the <=8-block chain  *)
(* covers only N = 1..8).  WBN_TAG_NIST_BRIDGE is the tag rewrite of the     *)
(* spine postcondition, under the band identifications                       *)
(* byteswap128 h = ghash_twist H and xi = word_reversefields 8 tag0.         *)
(* ------------------------------------------------------------------------- *)

let MAP_LIST_OF_SEQ = prove
 (`!(g:A->B) f n. MAP g (list_of_seq f n) = list_of_seq (g o f) n`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN GEN_TAC THEN
  ASM_REWRITE_TAC[LIST_OF_SEQ; MAP; o_THM] THEN REWRITE_TAC[o_ASSOC]);;

let LIST_OF_SEQ_NIST_INPUT_SYM = prove
 (`!ibytes N.
     list_of_seq (nist_input_block_bytes ibytes) N =
     MAP word_bytereverse
       (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes)) N)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MAP_LIST_OF_SEQ] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; nist_input_block_bytes; BREV_RF8_128]);;

let WBN_TAG_NIST_BRIDGE = prove
 (`!(H:int128) h xi tag0 ibytes nblk.
     byteswap128 h = ghash_twist H /\ xi = word_reversefields 8 tag0
     ==> word_bytereverse
           (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
             (MAP word_bytereverse
               (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes)) nblk))) =
         word_reversefields 8
           (nist_ghash H tag0 (list_of_seq (nist_input_block_bytes ibytes) nblk))`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[NIST_GHASH_IS_POLYVAL; LIST_OF_SEQ_NIST_INPUT_SYM; BREV_RF8_128] THEN
  REWRITE_TAC[GSYM BREV_RF8_128; WORD_BYTEREVERSE_BYTEREVERSE]);;

(* ------------------------------------------------------------------------- *)
(* Output-side bridge lemmas (no simulation, symbolic nblk).                 *)
(*                                                                           *)
(* The symbolic-nblk analogues of GCM_DEC_PT_BYTES_WHOLE_k and               *)
(* BYTE_LIST_AT_WHOLE_CTR of the <=8-block chain: they turn the nblk-uniform *)
(* per-block store forall of wbn_end_post into                               *)
(* byte_list_at (gcm_dec_pt_bytes ..).                                       *)
(* ------------------------------------------------------------------------- *)

(* EL of gcm_dec_blocks_from at a symbolic index (the analogue of
   build_aes_ctr_el). *)
let EL_GCM_DEC_BLOCKS_FROM = prove
 (`!m base i x. i < m
     ==> EL i (gcm_dec_blocks_from base m x) =
         bytes_to_int128 (SUB_LIST (16 * (base + i),16) x)`,
  INDUCT_TAC THEN REWRITE_TAC[LT] THEN
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THEN
  REWRITE_TAC[GCM_DEC_BLOCKS_FROM_STEP; EL; HD; TL] THENL
   [REWRITE_TAC[ADD_CLAUSES];
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`base + 1`; `n:num`; `x:byte list`]) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `(base + 1) + n = base + SUC n` SUBST1_TAC THENL
     [ARITH_TAC; REFL_TAC]]);;

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
                LENGTH_INT128_TO_BYTES] THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `j < n ==> MIN 16 (16 * n - 16 * j) = 16`];
      X_GEN_TAC `i:num` THEN REWRITE_TAC[LENGTH_INT128_TO_BYTES] THEN
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

(* ------------------------------------------------------------------------- *)
(* Counter-model bridge to the NIST SP 800-38D nonce||counter form of the    *)
(* other AES-GCM proofs, for the nonce-named keystream of the exported       *)
(* theorems.                                                                 *)
(*                                                                           *)
(* This proof names counters gcm_ctr_inc_iter j ctr0, iterated from an       *)
(* opaque initial block ctr0.  The other proofs use                          *)
(*   ctr_block nonce ctr = word_join (nonce:96 word) (word ctr:int32)        *)
(* (NIST big-endian: a fixed 96-bit nonce and a 32-bit big-endian counter).  *)
(* These lemmas prove that the two models coincide: gcm_ctr_inc_iter is NIST *)
(* inc32 iterated on the nonce||counter block, conjugated by the byte        *)
(* reversal of the load, unconditionally (the 32-bit wrap is the intended    *)
(* mod 2^32 rollover).  GCM_CTR_INC_ITER_CTR_BLOCK lets the exported         *)
(* theorems name the nonce, through WBN_OUTPUT_POINTWISE_NONCE and           *)
(* GCM_CTR_INC_ITER_NIST_IVEC below.  ctr_block, inc32 on it                 *)
(* (INC32_CTR_BLOCK, ITER_INC32_CTR_BLOCK) and its relation to GCTR are      *)
(* in arm/proofs/utils/aes_gcm_spec.ml (loaded through aes_gcm_common.ml).   *)
(* ------------------------------------------------------------------------- *)

(* The bridge: gcm_ctr_inc_iter j ctr0 is the NIST nonce||counter block
   advanced by j, provided the byte-reversed ctr0 is nonce||c.  By
   GCM_CTR_INC_ITER_INC32 above, gcm_ctr_inc_iter j x is
   word_bytereverse (ITER j inc32 (word_bytereverse x)). *)
let GCM_CTR_INC_ITER_CTR_BLOCK = prove
 (`!j (nonce:96 word) c ctr0.
     word_bytereverse ctr0 = ctr_block nonce c
     ==> gcm_ctr_inc_iter j ctr0 = word_bytereverse (ctr_block nonce (c + j))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GCM_CTR_INC_ITER_INC32] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[ITER_INC32_CTR_BLOCK]);;

(* ========================================================================= *)
(* Roadmap of the theorems below.                                            *)
(*                                                                           *)
(* The exported theorems come at the end of the file, in the shared AES-GCM  *)
(* vocabulary of aes_gcm_spec.ml: the correctness contracts                  *)
(*   AES256_GCM_DEC_ALT_CORRECT                   the core, pc+28 to pc+4556 *)
(*   AES256_GCM_DEC_ALT_NOIBT_SUBROUTINE_CORRECT  the AAPCS64 wrapper        *)
(* for the trimmed code (that of a -DNO_IBT build),                          *)
(* AES256_GCM_DEC_ALT_SUBROUTINE_CORRECT for the full code (by               *)
(* ARM_ADD_IBT_RULE) with its all-zero-key instance                          *)
(* AES256_GCM_DEC_ALT_ZERO_KEY_CORRECT, and the matching safety theorems     *)
(* AES256_GCM_DEC_ALT_SAFE, AES256_GCM_DEC_ALT_NOIBT_SUBROUTINE_SAFE and     *)
(* AES256_GCM_DEC_ALT_SUBROUTINE_SAFE.  The correctness contracts are        *)
(* derived, without re-running any simulation, from two internal spines with *)
(* a free GHASH key H and byte-list input and output, by fixing the key      *)
(* words, H and the counter block to the shared FIPS-197 / NIST convention   *)
(* and restating the input and the output per block                          *)
(* (WBN_EXPORT_FROM_SPINE_TAC):                                              *)
(*   WBN_DEC_CORE_BYTELIST        the core, pc+0x1c to pc+4556               *)
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
(*               exit pc+4556 (0x11cc), through the cascade or the exact-8   *)
(*               drain                                                       *)
(* with WBN_LOOP_PREP_EXT2 = loop ; prepretail,                              *)
(* WBN_FRONT_TO_PREP_EXT2 = front ; loop ; prepretail,                       *)
(* WBN_FRONT_TO_PREP_EXT2_916 = front ; prepretail and                       *)
(* WBN_FRONT_TO_END(_916) = WBN_FRONT_TO_PREP_EXT2(_916) ; tail.             *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* WBN_DEC_CORE_BYTELIST: the core spine, pc+0x1c to pc+4556, for every      *)
(* nblk >= 1, with H free and the output as the whole-buffer byte list; the  *)
(* exported AES256_GCM_DEC_ALT_CORRECT is derived from it.                   *)
(*                                                                           *)
(* The statement is written out in full.  It is the DISPATCH statement with  *)
(* nblk <= 8 replaced by 1 <= nblk and with the two size premises            *)
(* 128 * nblk < 2 EXP 64 and val in_p + 16 * nblk < 2 EXP 63 added: for      *)
(* nblk <= 8 they follow from the small nblk, for a symbolic nblk they rule  *)
(* out pointer and length overflow.  (The exported subroutine theorem gets   *)
(* the first from the 64-bit bit_len and keeps the second as a               *)
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
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p nblk ibytes rk H
    tag0 ctr0.
    1 <= nblk /\
    128 * nblk < 2 EXP 64 /\
    val in_p + 16 * nblk < 2 EXP 63 /\
    LENGTH ibytes = 16 * nblk /\
    LENGTH rk = 15 /\
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16]
    [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,240; htbl_p,192; stackpointer,80] /\
    PAIRWISE nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16] /\
    ALL (nonoverlapping (stackpointer,80))
    [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,240; htbl_p,192]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
              read PC s = word (pc + 28) /\
              read SP s = stackpointer /\
              C_ARGUMENTS
                [in_p; word (128 * nblk); out_p; xi_p; ivec_p; key_p; htbl_p]
                s /\
              byte_list_at ibytes in_p (word (16 * nblk)) s /\
              read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
              read (memory :> bytes128 ivec_p) s = ctr0 /\
              wordlist_from_memory (key_p,15) s = rk /\
              htable_mem_8 (ghash_twist H) htbl_p s)
         (\s. read PC s = word (pc + 4556) /\
              read X9 s = word (16 * nblk) /\
              byte_list_at (gcm_dec_pt_bytes (16 * nblk) ibytes ctr0 rk) out_p
              (word (16 * nblk)) s /\
              read (memory :> bytes128 xi_p) s =
              word_reversefields 8
              (nist_ghash H tag0
              (list_of_seq (nist_input_block_bytes ibytes) nblk)) /\
              read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter nblk ctr0)
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
          [memory :> bytes (out_p,16 * nblk); memory :> bytes (xi_p,16);
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
(* (through WBN_DEC_VALID_CALL_CORRECT).  It covers bit_len = 128 * nblk for *)
(* any nblk, so it is the whole-blocks contract of the function: for         *)
(* nblk = 0 the entry cbz x1 is taken and the function returns 0, with the   *)
(* output empty and the tag unchanged; for nblk >= 1 the entry guard falls   *)
(* through and the prologue, the core and the epilogue run.                  *)
(*                                                                           *)
(* The code: the entry guard (cbz x1; tst x1,#127; b.ne, at 0x0..0x8) comes  *)
(* before the d8-d15 spills (stp d8,d9,[sp,#-80]! and three more stp, at     *)
(* 0xc..0x18); the core runs from pc+0x1c to its exit pc+0x11cc (pc+4556);   *)
(* the epilogue (mov x0,x9; the ldp of d10..d15; ldp d8,d9,[sp],#80; ret, at *)
(* 0x11cc..0x11e0) restores the registers.  X30 is not saved; ret returns    *)
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
   (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p nblk ibytes rk H
      tag0 ctr0 returnaddress.
      128 * nblk < 2 EXP 64 /\
      val in_p + 16 * nblk < 2 EXP 63 /\
      LENGTH ibytes = 16 * nblk /\
      LENGTH rk = 15 /\
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16]
      [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,240; htbl_p,192;
       word_sub stackpointer (word 80),80] /\
      PAIRWISE nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16] /\
      ALL (nonoverlapping (word_sub stackpointer (word 80),80))
      [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,240; htbl_p,192]
      ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
               read PC s = word pc /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS
               [in_p; word (128 * nblk); out_p; xi_p; ivec_p; key_p; htbl_p]
               s /\
               byte_list_at ibytes in_p (word (16 * nblk)) s /\
               read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,15) s = rk /\
               htable_mem_8 (ghash_twist H) htbl_p s)
          (\s. read PC s = returnaddress /\
               C_RETURN s = word (16 * nblk) /\
               byte_list_at (gcm_dec_pt_bytes (16 * nblk) ibytes ctr0 rk) out_p
               (word (16 * nblk)) s /\
               read (memory :> bytes128 xi_p) s =
               word_reversefields 8
               (nist_ghash H tag0 (list_of_seq (nist_input_block_bytes ibytes) nblk)) /\
               read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter nblk ctr0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE
           [memory :> bytes (out_p,16 * nblk); memory :> bytes (xi_p,16);
            memory :> bytes (ivec_p,16);
            memory :> bytes (word_sub stackpointer (word 80),80)])`,
  (* The wrapper is written by hand (see above); these helpers are local to the
     proof. *)
  let EXEC = AES256_GCM_DEC_ALT_EXEC in
  (* the core, SP set to the post-prologue in-frame value *)
  let WB_CORE_INST =
    SPECL [`pc:num`; `word_sub stackpointer (word 80):int64`;
           `in_p:int64`; `out_p:int64`; `xi_p:int64`; `ivec_p:int64`;
           `key_p:int64`; `htbl_p:int64`; `nblk:num`; `ibytes:byte list`;
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
  (* guard fall-through: cbz/b.ne both fall through for bit_len = 128*nblk *)
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
       function returns 0 in X0 touching no memory (L256_dec_ret at 0x173c:
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

(* The counter write-back: the spines' gcm_ctr_inc_iter n, started from the  *)
(* shared ivec value for counter c, is the shared ivec value for n + c.      *)
let GCM_CTR_INC_ITER_NIST_IVEC = prove
 (`!n (nonce:96 word) c.
     gcm_ctr_inc_iter n (word_reversefields 8 (ctr_block nonce c)) =
     word_reversefields 8 (ctr_block nonce (n + c))`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`n:num`; `nonce:96 word`; `c:num`;
                `word_reversefields 8 (ctr_block nonce c)`]
    GCM_CTR_INC_ITER_CTR_BLOCK) THEN
  REWRITE_TAC[BREV_RF8_INV_128] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[BREV_RF8_128; ADD_SYM]);;

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

(* ------------------------------------------------------------------------- *)
(* The exported contracts, in the shared AES-GCM vocabulary.                 *)
(*                                                                           *)
(* AES256_GCM_DEC_ALT_CORRECT (the core, pc+28 to pc+4556) and               *)
(* WBN_DEC_VALID_CALL_CORRECT (the AAPCS64 wrapper at bit_len = 128 * nblk)  *)
(* are lifted from the two spines by WBN_EXPORT_FROM_SPINE_TAC: the key      *)
(* words, the GHASH key and the counter block are pinned to the FIPS-197 /   *)
(* NIST convention and the input and output are restated per block.          *)
(* AES256_GCM_DEC_ALT_NOIBT_SUBROUTINE_CORRECT (any bit_len) adds the reject *)
(* path of the entry guard to WBN_DEC_VALID_CALL_CORRECT.  These are about   *)
(* the trimmed code; AES256_GCM_DEC_ALT_SUBROUTINE_CORRECT, about the full   *)
(* code, follows from the NOIBT one by ARM_ADD_IBT_RULE.  c is the free      *)
(* counter of data block 0: the kernel increments whatever ivec holds, and   *)
(* c = 2 is the standard NIST SP 800-38D instance.  The machine code writes  *)
(* every one of the 32 vector registers; beyond the ABI frame, the core      *)
(* frame lists Q8-Q15 (WB_CORE_FRAME_EQ below).                              *)
(* ------------------------------------------------------------------------- *)

(* The frame of the two core theorems (correctness and safety).
   MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI already covers Q0-Q7, Q16-Q31 and
   the top halves of Q8-Q15, so beyond it the core theorems list only Q8-Q15,
   whose bottom halves d8-d15 the prologue saves before the core and the
   epilogue restores after it.  This is the same frame as the internal spines',
   which list all of Q0-Q31: the two are equal, so stating the shorter one
   weakens nothing, and the proofs rewrite it back to the spines' form. *)
let WB_SUBSUMED_ANTISYM = prove
 (`!(R:A->B->bool) S. R subsumed S /\ S subsumed R ==> R = S`,
  REWRITE_TAC[subsumed; FUN_EQ_THM] THEN MESON_TAC[]);;

let WB_CORE_FRAME_EQ = prove
 (`!stackpointer out_p xi_p ivec_p nblk.
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE
      [memory :> bytes (out_p,16 * nblk); memory :> bytes (xi_p,16);
       memory :> bytes (ivec_p,16);
       memory :> bytes (word_add stackpointer (word 64),16)] ,,
      MAYCHANGE
      [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13; Q14;
       Q15; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23; Q24; Q25; Q26; Q27;
       Q28; Q29; Q30; Q31]) =
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE
      [memory :> bytes (out_p,16 * nblk); memory :> bytes (xi_p,16);
       memory :> bytes (ivec_p,16);
       memory :> bytes (word_add stackpointer (word 64),16)] ,,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15])`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC WB_SUBSUMED_ANTISYM THEN CONJ_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  SUBSUMED_MAYCHANGE_TAC);;

(* The exported core contract (after the prologue, bit_len = 128 * nblk). *)
let AES256_GCM_DEC_ALT_CORRECT = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p nblk inblock rk
    tag0 nonce c.
    1 <= nblk /\
    128 * nblk < 2 EXP 64 /\
    val in_p + 16 * nblk < 2 EXP 63 /\
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16]
    [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,240; htbl_p,192; stackpointer,80] /\
    PAIRWISE nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16] /\
    ALL (nonoverlapping (stackpointer,80))
    [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,240; htbl_p,192]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
              read PC s = word (pc + 28) /\
              read SP s = stackpointer /\
              C_ARGUMENTS
              [in_p; word (128 * nblk); out_p; xi_p; ivec_p; key_p; htbl_p]
              s /\
              (!j. j < nblk
                   ==> read (memory :> bytes128
                              (word_add in_p (word (16 * j)))) s = inblock j) /\
              read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
              read (memory :> bytes128 ivec_p) s =
              word_reversefields 8 (ctr_block nonce c) /\
              wordlist_from_memory (key_p,15) s =
              MAP (word_reversefields 8) rk /\
              htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htbl_p s)
         (\s. read PC s = word (pc + 4556) /\
              read X9 s = word (16 * nblk) /\
              (!j. j < nblk
                   ==> read (memory :> bytes128
                              (word_add out_p (word (16 * j)))) s =
                       word_xor (aes_ctr_block aes256_cipher c nonce rk j)
                                (inblock j)) /\
              read (memory :> bytes128 xi_p) s =
              word_reversefields 8
              (nist_ghash (aes256_cipher (word 0) rk) tag0
              (list_of_seq (nist_input_block inblock) nblk)) /\
              read (memory :> bytes128 ivec_p) s =
              word_reversefields 8 (ctr_block nonce (nblk + c)))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
          [memory :> bytes (out_p,16 * nblk);
           memory :> bytes (xi_p,16);
           memory :> bytes (ivec_p,16);
           memory :> bytes (word_add stackpointer (word 64),16)] ,,
          MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15])`,
  PURE_REWRITE_TAC[GSYM WB_CORE_FRAME_EQ] THEN
  WBN_EXPORT_FROM_SPINE_TAC WBN_DEC_CORE_BYTELIST);;

(* The whole-block subroutine result for bit_len = 128 * nblk, any nblk      *)
(* including 0: an internal helper for the public arbitrary-length theorem.  *)
let WBN_DEC_VALID_CALL_CORRECT = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p nblk inblock rk
    tag0 nonce c returnaddress.
    128 * nblk < 2 EXP 64 /\
    val in_p + 16 * nblk < 2 EXP 63 /\
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16]
    [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,240; htbl_p,192;
     word_sub stackpointer (word 80),80] /\
    PAIRWISE nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16] /\
    ALL (nonoverlapping (word_sub stackpointer (word 80),80))
    [word pc, LENGTH aes256_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,240; htbl_p,192]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
              read PC s = word pc /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS
              [in_p; word (128 * nblk); out_p; xi_p; ivec_p; key_p; htbl_p]
              s /\
              (!j. j < nblk
                   ==> read (memory :> bytes128
                              (word_add in_p (word (16 * j)))) s = inblock j) /\
              read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
              read (memory :> bytes128 ivec_p) s =
              word_reversefields 8 (ctr_block nonce c) /\
              wordlist_from_memory (key_p,15) s =
              MAP (word_reversefields 8) rk /\
              htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htbl_p s)
         (\s. read PC s = returnaddress /\
              C_RETURN s = word (16 * nblk) /\
              (!j. j < nblk
                   ==> read (memory :> bytes128
                              (word_add out_p (word (16 * j)))) s =
                       word_xor (aes_ctr_block aes256_cipher c nonce rk j)
                                (inblock j)) /\
              read (memory :> bytes128 xi_p) s =
              word_reversefields 8
              (nist_ghash (aes256_cipher (word 0) rk) tag0
              (list_of_seq (nist_input_block inblock) nblk)) /\
              read (memory :> bytes128 ivec_p) s =
              word_reversefields 8 (ctr_block nonce (nblk + c)))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
          [memory :> bytes (out_p,16 * nblk); memory :> bytes (xi_p,16);
           memory :> bytes (ivec_p,16);
           memory :> bytes (word_sub stackpointer (word 80),80)])`,
  WBN_EXPORT_FROM_SPINE_TAC WBN_DEC_SUBROUTINE_BYTELIST);;

(* The exported subroutine contract (the AAPCS64-callable result), for an
   arbitrary bit_len, first for the trimmed code, the code of a -DNO_IBT
   build.  gcm_wb_blocks bit_len is the number of blocks processed, and
   every data-dependent clause is indexed by it, so one postcondition
   describes all three paths:
   - a non-multiple of 128 is rejected by the entry guard (cbz falls through,
     tst/b.ne branches to the return), which returns 0 and touches no memory;
   - zero and the nonzero multiples of 128 are WBN_DEC_VALID_CALL_CORRECT at
     bit_len = word (128 * nblk), where 128 * nblk < 2 EXP 64 is just
     VAL_BOUND_64.
   The pointer bound val in_p + 16 * nblk < 2 EXP 63 is genuine: the kernel
   compares pointers with signed conditions.
   This routine does not enforce the NIST GCM message limit. Callers must
   ensure the cumulative message length does not exceed 2^36 - 32 bytes
   (2^39 - 256 bits). *)
let AES256_GCM_DEC_ALT_NOIBT_SUBROUTINE_CORRECT = prove
 (`!pc stackpointer in_p bit_len out_p xi_p ivec_p key_p htbl_p inblock rk
    tag0 nonce c returnaddress.
    val in_p + 16 * gcm_wb_blocks bit_len < 2 EXP 63 /\
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping
    [out_p,16 * gcm_wb_blocks bit_len; xi_p,16; ivec_p,16]
    [word pc, LENGTH aes256_gcm_dec_alt_tmc;
     in_p,16 * gcm_wb_blocks bit_len; key_p,240; htbl_p,192;
     word_sub stackpointer (word 80),80] /\
    PAIRWISE nonoverlapping
    [out_p,16 * gcm_wb_blocks bit_len; xi_p,16; ivec_p,16] /\
    ALL (nonoverlapping (word_sub stackpointer (word 80),80))
    [word pc, LENGTH aes256_gcm_dec_alt_tmc;
     in_p,16 * gcm_wb_blocks bit_len; key_p,240; htbl_p,192]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
              read PC s = word pc /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS
              [in_p; bit_len; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
              (!j. j < gcm_wb_blocks bit_len
                   ==> read (memory :> bytes128
                              (word_add in_p (word (16 * j)))) s = inblock j) /\
              read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
              read (memory :> bytes128 ivec_p) s =
              word_reversefields 8 (ctr_block nonce c) /\
              wordlist_from_memory (key_p,15) s =
              MAP (word_reversefields 8) rk /\
              htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htbl_p s)
         (\s. read PC s = returnaddress /\
              C_RETURN s = word (16 * gcm_wb_blocks bit_len) /\
              (!j. j < gcm_wb_blocks bit_len
                   ==> read (memory :> bytes128
                              (word_add out_p (word (16 * j)))) s =
                       word_xor (aes_ctr_block aes256_cipher c nonce rk j)
                                (inblock j)) /\
              read (memory :> bytes128 xi_p) s =
              word_reversefields 8
              (nist_ghash (aes256_cipher (word 0) rk) tag0
              (list_of_seq (nist_input_block inblock)
                           (gcm_wb_blocks bit_len))) /\
              read (memory :> bytes128 ivec_p) s =
              word_reversefields 8
                (ctr_block nonce (gcm_wb_blocks bit_len + c)))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
          [memory :> bytes
             (out_p,16 * gcm_wb_blocks bit_len);
           memory :> bytes (xi_p,16);
           memory :> bytes (ivec_p,16);
           memory :> bytes (word_sub stackpointer (word 80),80)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `nblk = gcm_wb_blocks bit_len` THEN
  ASM_CASES_TAC `val(bit_len:int64) MOD 128 = 0` THENL
   [(* Whole blocks, including zero: bit_len = word (128 * nblk). *)
    SUBGOAL_THEN `val(bit_len:int64) = 128 * nblk` ASSUME_TAC THENL
     [EXPAND_TAC "nblk" THEN ASM_SIMP_TAC[GCM_WB_BLOCKS_VALID];
      ALL_TAC] THEN
    SUBGOAL_THEN `128 * nblk < 2 EXP 64` ASSUME_TAC THENL
     [MP_TAC(ISPEC `bit_len:int64` VAL_BOUND_64) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `bit_len:int64 = word (128 * nblk)` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(fun th ->
        if concl th = `val(bit_len:int64) = 128 * nblk`
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
  SUBGOAL_THEN `~(val(bit_len:int64) = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~(val(bit_len:int64) MOD 128 = 0)` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(val(word_and (bit_len:int64) (word 127)) = 0)`
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
 (`!pc stackpointer in_p bit_len out_p xi_p ivec_p key_p htbl_p inblock rk
    tag0 nonce c returnaddress.
    val in_p + 16 * gcm_wb_blocks bit_len < 2 EXP 63 /\
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping
    [out_p,16 * gcm_wb_blocks bit_len; xi_p,16; ivec_p,16]
    [word pc, LENGTH aes256_gcm_dec_alt_mc;
     in_p,16 * gcm_wb_blocks bit_len; key_p,240; htbl_p,192;
     word_sub stackpointer (word 80),80] /\
    PAIRWISE nonoverlapping
    [out_p,16 * gcm_wb_blocks bit_len; xi_p,16; ivec_p,16] /\
    ALL (nonoverlapping (word_sub stackpointer (word 80),80))
    [word pc, LENGTH aes256_gcm_dec_alt_mc;
     in_p,16 * gcm_wb_blocks bit_len; key_p,240; htbl_p,192]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_mc /\
              read PC s = word pc /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS
              [in_p; bit_len; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
              (!j. j < gcm_wb_blocks bit_len
                   ==> read (memory :> bytes128
                              (word_add in_p (word (16 * j)))) s = inblock j) /\
              read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
              read (memory :> bytes128 ivec_p) s =
              word_reversefields 8 (ctr_block nonce c) /\
              wordlist_from_memory (key_p,15) s =
              MAP (word_reversefields 8) rk /\
              htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htbl_p s)
         (\s. read PC s = returnaddress /\
              C_RETURN s = word (16 * gcm_wb_blocks bit_len) /\
              (!j. j < gcm_wb_blocks bit_len
                   ==> read (memory :> bytes128
                              (word_add out_p (word (16 * j)))) s =
                       word_xor (aes_ctr_block aes256_cipher c nonce rk j)
                                (inblock j)) /\
              read (memory :> bytes128 xi_p) s =
              word_reversefields 8
              (nist_ghash (aes256_cipher (word 0) rk) tag0
              (list_of_seq (nist_input_block inblock)
                           (gcm_wb_blocks bit_len))) /\
              read (memory :> bytes128 ivec_p) s =
              word_reversefields 8
                (ctr_block nonce (gcm_wb_blocks bit_len + c)))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
          [memory :> bytes
             (out_p,16 * gcm_wb_blocks bit_len);
           memory :> bytes (xi_p,16);
           memory :> bytes (ivec_p,16);
           memory :> bytes (word_sub stackpointer (word 80),80)])`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
    ~extra:[htable_mem_8; htable_mem_4; wordlist_from_memory]
    aes256_gcm_dec_alt_mc aes256_gcm_dec_alt_tmc
    AES256_GCM_DEC_ALT_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* The exported theorem at the all-zero key.  With rk the FIPS-197 schedule  *)
(* of that key, the key table precondition of                                *)
(* AES256_GCM_DEC_ALT_SUBROUTINE_CORRECT rewrites, by                        *)
(* HTABLE_MEM_8_AESAVS_ZERO_KEY_256 at the top of this file, to the twelve   *)
(* 16-byte entries that gcm_init_v8 writes for the key, which are also the   *)
(* bytes the C test aes_gcm_htable checks.  So the table described by the    *)
(* exported statement itself, not only by the vocabulary it uses, is the     *)
(* real one; the load fails here if the precondition is not of that form.    *)
(* ------------------------------------------------------------------------- *)

let AES256_GCM_DEC_ALT_ZERO_KEY_CORRECT =
  let th = PURE_REWRITE_RULE[HTABLE_MEM_8_AESAVS_ZERO_KEY_256]
   (INST [`AESAVS_ZERO_KEY_256_SCHEDULE`,`rk:int128 list`]
     (SPEC_ALL AES256_GCM_DEC_ALT_SUBROUTINE_CORRECT)) in
  if can (find_term (fun t -> is_const t && fst(dest_const t) = "htable_mem_8"))
         (concl th)
  then failwith "AES256_GCM_DEC_ALT_ZERO_KEY_CORRECT: table not rewritten"
  else GEN_ALL th;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(*                                                                           *)
(* AES256_GCM_DEC_ALT_SAFE is the safety theorem of the core, from pc+0x1c   *)
(* to the core exit pc+4556, for bit_len = 128 * nblk with 1 <= nblk.        *)
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
(* bit_len (ARBITRARY_WRAPPER_SAFE_TAC), and                                 *)
(* AES256_GCM_DEC_ALT_SUBROUTINE_SAFE is its IBT lift (ARM_ADD_IBT_RULE).    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let EXEC = AES256_GCM_DEC_ALT_EXEC;;

(* ---- quiet stepper: the default one logs a line per state, and these legs
   run several hundred steps each ---- *)
let ARM_QSTEP_TAC th s =
  ARM_STEP_TAC th [] s None (K STRIP_TAC) THEN DISCARD_OLDSTATE_TAC s THEN CLARIFY_TAC;;
let ARM_QSTEPS_TAC th snums = MAP_EVERY (ARM_QSTEP_TAC th) (statenames "s" snums);;

(* ---- general affine word_sub cancellation (no WORD_BLAST) ----
   For a `word_sub P Q` subterm whose only free int64 variable is a single
   register base x (in_p, out_p, ...), the difference P - Q does not depend on
   x: prove `word_sub P Q = word_sub P[x:=0] Q[x:=0]` by WORD_RULE (the
   x-dependence cancels), then reduce the right side to a numeral `word k` by
   WORD_REDUCE_CONV. *)
let affine_cancel_thm t =
  match t with
  | Comb(Comb(Const("word_sub",_),_),_) ->
    let fv = filter (fun v -> type_of v = `:int64` && is_var v) (frees t) in
    (match fv with
     | [x] ->
       let t0 = subst [`word 0:int64`, x] t in
       let step1 = WORD_RULE (mk_eq(t, t0)) in
       (* |- word_sub P Q = word k *)
       CONV_RULE (RAND_CONV WORD_REDUCE_CONV) step1
     | _ -> failwith "affine_cancel_thm: not exactly one int64 var")
  | _ -> failwith "affine_cancel_thm: not word_sub";;

(* Collect every affine word_sub in the goal and the assumptions, cancel it,
   rewrite the assumptions with the results, then reduce the now concrete PC
   if-condition. *)
let WB_TAIL_RESOLVE_TAC : tactic = fun (asl,w) ->
  let is_sub tm = match tm with
    | Comb(Comb(Const("word_sub",_),_),_) ->
        length (filter (fun v -> type_of v = `:int64` && is_var v) (frees tm)) = 1
    | _ -> false in
  let all = itlist (fun (_,th) acc -> concl th :: acc) asl [w] in
  let subs = setify (itlist (fun t acc -> find_terms is_sub t @ acc) all []) in
  let cancel_thms = mapfilter affine_cancel_thm subs in
  (RULE_ASSUM_TAC(REWRITE_RULE cancel_thms) THEN
   (* reflexive compares: ival x - ival x and word_sub x x reduce to 0 *)
   RULE_ASSUM_TAC(REWRITE_RULE[INT_SUB_REFL; WORD_SUB_REFL; VAL_WORD_0; IVAL_WORD_0]) THEN
   RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV WORD_REDUCE_CONV)) THEN
   RULE_ASSUM_TAC(CONV_RULE(TRY_CONV INT_REDUCE_CONV)) THEN
   RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(DEPTH_CONV NUM_EQ_CONV))) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[NOT_CLAUSES; COND_CLAUSES]) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[])) (asl,w);;

(* ---- extract (current state index, PC offset) from the goal's PC assumption:
   the offset is n >= 0 for a concrete pc+n (or a bare word n), -2 for a
   symbolic if-term (which needs the resolver), -3 if there is no PC
   assumption. ---- *)
let pc_info (asl,_) =
  try
    let (_,th) = List.find (fun (_,th) -> match concl th with
        | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),_)),_) -> true
        | _ -> false) asl in
    let lhs,rhs = dest_eq (concl th) in
    let st = rand lhs in
    let sidx = (let nm = fst(dest_var st) in
                int_of_string (String.sub nm 1 (String.length nm - 1))) in
    let off = (match rhs with
      | Comb(Const("word",_),Comb(Comb(Const("+",_),_),n)) -> (try dest_small_numeral n with _ -> -2)
      | Comb(Const("word",_),n) -> (try dest_small_numeral n with _ -> -2)
      | _ -> -2) in
    (sidx, off)
  with _ -> (-1, -3);;

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
   open, then DRIVE from s0 to pc+4556, finalize.  Every branch condition on
   these bands is concrete arithmetic that the resolver reduces directly, so no
   band-specific step count is needed.  The bands 5..8 and 9..16 run a shared
   front instead (FRONT_58_CLOSE_TAC, front_916_sim_tac below). ---- *)
let concrete_band_close_tac =
  LEG_INIT_TAC THEN
  DRIVE_TAC 4556 700 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ---- the case split shared by the band and residue dispatches: assert
   `x = lo \/ ... \/ x = hi`, proved by side_tac, and leave the cases in order.
   BOUNDS_ARITH_TAC proves such a disjunction from the named bounds alone,
   without the rest of a leg's context. ---- *)
let WB_CASES_TAC x (lo,hi) side_tac =
  let disj = end_itlist (fun a b -> mk_disj(a,b))
     (map (fun k -> mk_eq(x, mk_small_numeral k)) (lo--hi)) in
  SUBGOAL_THEN disj MP_TAC THENL [side_tac; ALL_TAC] THEN STRIP_TAC;;

let BOUNDS_ARITH_TAC bnds =
  MAP_EVERY (MP_TAC o ASSUME) bnds THEN POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;;

(* ---- n-way split of a bounded nblk leg lo..hi, then close each band ---- *)
let split_close_tac lo hi =
  WB_CASES_TAC `nblk:num` (lo,hi) ASM_ARITH_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  concrete_band_close_tac;;

(* ---- reusable safety back-legs, from the compare just before the correctness
   proof's q_at seam.  There X5 is the public residual byte count; the theorem
   executes the compare and the initial ciphertext and H^8 loads itself, so its
   interface carries no condition-code assumptions.  From here the trace
   depends only on the public addresses and the fixed residual block count; all
   SIMD and data values may stay unconstrained.

   Each residual tail is proved once, against the caller's whole-buffer bounds.
   The selected witnesses below are closed choice terms, so all three consumers
   (5..8, 9..16 and >=17) reuse them without an existential witness escaping
   its scope. ---- *)
let WB_SAFETY_BYTES_LEN = prove
 (`!nblk.
      128 * nblk < 2 EXP 64
      ==> val (word (128 * nblk):int64) DIV 8 * 1 = 16 * nblk`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  MP_TAC(SPECL [`8`; `16 * nblk`] DIV_MULT) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* The val-free twin of the above, needed on the >=17 leg only.
   WB_SAFETY_BYTES_LEN matches `val (word (128*nblk)) DIV 8 * 1`, but by the
   time the >=17 residue reaches its events discharge the goal's bound is
   already spelled `(128 * nblk) DIV 8 * 1`: CORE_SAFE_OPEN_TAC asserts
   `val (word (128*nblk)) = 128*nblk` into the assumptions, and
   WB_TAIL_POST_ASM_REWRITE_TAC (which rewrites with every `val`-headed
   assumption) consumes the `val (word ...)` wrapper on the goal side.  The
   assumption side, stripped straight off the reusable tail theorem, keeps the
   val spelling.  So WB_SAFETY_BYTES_LEN cannot fire on the goal, and the two
   sides end up as `(128*nblk) DIV 8 * 1` and `16*nblk`.  This rule closes that
   gap.  It needs no size side condition: with the word wrapper gone it is pure
   natural-number arithmetic, which is also why it is safe to keep
   unconditionally in the rewrite set.  The 9..16 bands never need it (nblk is
   a numeral there, so NUM_REDUCE collapses the bound outright). *)
let WB_SAFETY_BYTES_LEN_NOVAL = prove
 (`!nblk. (128 * nblk) DIV 8 * 1 = 16 * nblk`,
  GEN_TAC THEN
  MP_TAC(SPECL [`8`; `16 * nblk`] DIV_MULT) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* memaccess_inbounds distributes over a loop trace: if every iteration's own
   trace is in bounds, so is the concatenation ENUMERATEL builds.  Needed on
   the >=17 leg only, whose scaffold keeps the loop body symbolic in `i`; the
   legs for nblk <= 16 do not run the loop and produce no ENUMERATEL goal.  The
   stock DISCHARGE_MEMACCESS_INBOUNDS_TAC (common/consttime.ml) splits traces
   with MEMACCESS_INBOUNDS_APPEND (common/safety.ml) but has no ENUMERATEL
   rule, so a quantified loop trace matches none of its cases. *)
let MEMACCESS_INBOUNDS_ENUMERATEL = prove
 (`!n (f:num->((N)address_uarch_event)list) rr ww.
     (!i. i < n ==> memaccess_inbounds (f i) rr ww)
     ==> memaccess_inbounds (ENUMERATEL n f) rr ww`,
  INDUCT_TAC THEN REWRITE_TAC[ENUMERATEL] THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[memaccess_inbounds_def; ALL];
    REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[LT] THEN
      DISCH_THEN MATCH_ACCEPT_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

let WB_CONTAINED_REFL = prove
 (`!(x:N word) n. contained (x,n) (x,n)`,
  REWRITE_TAC[CONTAINED] THEN MESON_TAC[]);;

let WB_FIRST_NONOVERLAPPING_TAC : tactic = fun (asl,w) ->
  try FIRST_ASSUM ACCEPT_TAC (asl,w)
  with Failure _ ->
    (ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN
     FIRST_ASSUM ACCEPT_TAC) (asl,w);;

(* DISCHARGE_SAFETY_PROPERTY_TAC with its closing memaccess_inbounds tactic
   replaced by meminb_tac: the shape of DISCHARGE_SAFE_ROBUST
   (aes_gcm_common.ml). *)
let WB_SAFETY_PROPERTY_TAC (meminb_tac:tactic) : tactic =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W (fun (asl,w) ->
    (if is_conj w then
       CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC]
     else ALL_TAC) THEN
    meminb_tac);;

let mk_tail_safe_goal r =
  subst [mk_small_numeral r,`rr:num`]
   `exists f_events.
      forall e pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p nblk
             tail_in tail_out.
        1 <= nblk /\
        128 * nblk < 2 EXP 64 /\
        contained (tail_in,16 * rr) (in_p,16 * nblk) /\
        contained (tail_out,16 * rr) (out_p,16 * nblk) /\
        nonoverlapping
          (word pc,LENGTH aes256_gcm_dec_alt_tmc) (stackpointer,80) /\
        ALLPAIRS nonoverlapping
          [out_p,16 * nblk; xi_p,16; ivec_p,16]
          [word pc,LENGTH aes256_gcm_dec_alt_tmc]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
                  read PC s = word (pc + 0xee4) /\
                  read X0 s = tail_in /\
                  read X2 s = tail_out /\
                  read X3 s = xi_p /\
                  read X5 s = word (16 * rr) /\
                  read X6 s = htbl_p /\
                  read X10 s = word_add stackpointer (word 64) /\
                  read X16 s = ivec_p /\
                  read events s = e)
             (\s. read PC s = word (pc + 4556) /\
                  (exists e2.
                       read events s = APPEND e2 e /\
                       e2 =
                       f_events in_p key_p htbl_p out_p xi_p ivec_p nblk
                                tail_in tail_out pc stackpointer /\
                       memaccess_inbounds e2
                       [in_p,16 * nblk; xi_p,16; ivec_p,16;
                        key_p,240; htbl_p,192; out_p,16 * nblk;
                        stackpointer,80]
                       [out_p,16 * nblk; xi_p,16; ivec_p,16;
                        stackpointer,80]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
              [memory :> bytes (tail_out,16 * rr); memory :> bytes (xi_p,16);
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
      `nonoverlapping (word pc,5956) (tail_out:int64,tail_len)` in
  let tail_reads =
    subst [tail_len,`tail_len:num`]
      `[(tail_in:int64),tail_len; xi_p,16; ivec_p,16; key_p,240; htbl_p,192;
        tail_out,tail_len; stackpointer,80]` in
  let tail_writes =
    subst [tail_len,`tail_len:num`]
      `[(tail_out:int64),tail_len; xi_p,16; ivec_p,16; stackpointer,80]` in
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
     [`nonoverlapping (word pc,5956) (out_p:int64,16 * nblk)`;
      `nonoverlapping (word pc,5956) (xi_p:int64,16)`;
      `nonoverlapping (word pc,5956) (ivec_p:int64,16)`] THEN
    SUBGOAL_THEN tail_code_nonoverlap ASSUME_TAC THENL
     [MATCH_MP_TAC NONOVERLAPPING_SUBREGIONS THEN
      MAP_EVERY EXISTS_TAC
       [`word pc:int64`; `5956`; `out_p:int64`; `16 * nblk`] THEN
      ASM_REWRITE_TAC[WB_CONTAINED_REFL];
      ALL_TAC] THEN
    SUBGOAL_THEN
      `val (word (128 * nblk):int64) DIV 8 * 1 = 16 * nblk`
      SUBST_ALL_TAC THENL
     [MATCH_MP_TAC WB_SAFETY_BYTES_LEN THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    DRIVE_TAC 4556 400 THEN
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

(* The accumulated event trace of state st: the right side of its
   `read events st` assumption. *)
let events_of_state asl st =
  rhs(concl(snd(find (fun (_,th) ->
    let c = concl th in
    is_eq c &&
    (try rator(lhs c) = `read events` && rand(lhs c) = st with _ -> false))
    asl)));;

(* Specialize the selected r-block tail theorem to a leg with block count nblk
   whose residual tail reads tail_in and writes tail_out, at the current
   accumulated event trace of state sname.  Using the state equation's right
   side keeps the old state variable from surviving ARM_BIGSTEP_TAC's
   cleanup. *)
let MP_WB_TAIL_SAFE_TAC r sname nblk tail_in tail_out : tactic =
  let args =
    [`pc:num`; `stackpointer:int64`; `in_p:int64`; `out_p:int64`;
     `xi_p:int64`; `ivec_p:int64`; `key_p:int64`; `htbl_p:int64`;
     nblk; tail_in; tail_out] in
  fun (asl,w) ->
    let ev = events_of_state asl (mk_var(sname,`:armstate`)) in
    MP_TAC(SPECL (ev :: args) (el (r-1) wbn_tail_safeties)) (asl,w);;

(* These back-legs already finish at the enclosing safety theorem's final PC.
   Consume their ensures theorem directly instead of passing it through
   ARM_BIGSTEP_TAC: the latter needlessly rebuilds the whole state update and
   can fail while absorbing the nested MAYCHANGE relation. *)
let FINAL_TAIL_ENSURES = prove
 (`!step (P:S->bool) Q C Q' C' s.
      P s /\
      ensures step P Q C /\
      C subsumed C' /\
      (!s'. Q s' ==> Q' s')
      ==> eventually step (\s'. Q' s' /\ C' s s') s`,
  REWRITE_TAC[ensures; subsumed] THEN
  MESON_TAC[EVENTUALLY_MONO]);;

(* When the tail starts after a simulated prefix, compose its frame with the
   enclosing frame from the original state instead of rebasing that frame at
   the tail state.

   COMPOSE_FRAME_LEMMA is split out so that MESON only ever sees the frame
   composition.  Handed the whole composed statement instead, MESON diverges:
   the `seq` existential multiplies with `eventually`'s own quantifier. *)
let COMPOSE_FRAME_LEMMA = prove
 (`(C' ,, C) subsumed C' ==> C' s0 s /\ C s s' ==> C' s0 s'`,
  REWRITE_TAC[subsumed; seq] THEN MESON_TAC[]);;

let FINAL_COMPOSED_TAIL_ENSURES = prove
 (`!step (P:S->bool) Q C Q' C' s0 s.
      C' s0 s /\
      P s /\
      ensures step P Q C /\
      (C' ,, C) subsumed C' /\
      (!s'. Q s' ==> Q' s')
      ==> eventually step (\s'. Q' s' /\ C' s0 s') s`,
  REWRITE_TAC[ensures] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(MATCH_MP th (ASSUME `(P:S->bool) s`))) THEN
  MATCH_MP_TAC(REWRITE_RULE[GSYM RIGHT_FORALL_IMP_THM] EVENTUALLY_MONO) THEN
  BETA_TAC THEN X_GEN_TAC `t:S` THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[];
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP COMPOSE_FRAME_LEMMA o
                  check (fun th -> is_binary "subsumed" (concl th))) THEN
    ASM_REWRITE_TAC[]]);;

(* Consume a tail theorem, discharged from the goal, through one of the two
   finishing lemmas above: front closes the lemma's conjuncts that precede the
   tail's own ensures, which is then the tail theorem, followed by its frame
   and, by post_tac, the enclosing postcondition. *)
let CONSUME_WB_TAIL_TAC lemma (front:tactic list) post_tac : tactic =
  DISCH_THEN(fun tailth ->
    let _,args = strip_comb(concl tailth) in
    let tail_pre = el 1 args
    and tail_post = el 2 args
    and tail_frame = el 3 args in
    MATCH_MP_TAC lemma THEN
    MAP_EVERY EXISTS_TAC [tail_pre; tail_post; tail_frame] THEN
    REPEAT CONJ_TAC THENL
     (front @
      [ACCEPT_TAC tailth;
       REWRITE_TAC[ETA_AX; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                   MODIFIABLE_SIMD_REGS; MODIFIABLE_GPRS;
                   MODIFIABLE_UPPER_SIMD_REGS] THEN
       SUBSUMED_MAYCHANGE_TAC;
       post_tac]));;

let USE_WB_TAIL_SAFE_TAC =
  CONSUME_WB_TAIL_TAC FINAL_TAIL_ENSURES [BETA_TAC THEN ASM_REWRITE_TAC[]];;

let USE_WB_COMPOSED_TAIL_SAFE_TAC =
  CONSUME_WB_TAIL_TAC FINAL_COMPOSED_TAIL_ENSURES
   [MONOTONE_MAYCHANGE_TAC;
    (* On legs whose tail is entered after a long symbolic front, the front can
       leave the leftover-byte count in X5 as the unreduced difference
       `word_sub (in_p + 16*nblk) (in_p + 128*k)`; the blanket rewrite then
       closes 9 of the 10 precondition conjuncts and leaves that word equation,
       which WORD_RULE finishes.  Where X5 is already reduced nothing is left,
       hence TRY. *)
    BETA_TAC THEN ASM_REWRITE_TAC[] THEN TRY(CONV_TAC WORD_RULE)];;

(* ---- net-safe rewriting for the composed tails.  On the 9..16 and >=17 legs,
   which reach their tail after a long symbolic front, the assumption list
   carries that front's per-state reads plus front_916_setup_tac's asserted
   USHR, AND-mask and DIVISION identities, among which are cyclic equation
   pairs.  A rewrite net (REWRITE_TAC, ASM_SIMP_TAC, any TOP_DEPTH traversal)
   re-descends into its own output and diverges on such a pair, overflowing the
   stack ("looping recursion?"); narrowing the assumption set alone does not
   prevent it.  A single ONCE_DEPTH pass rewrites every redex at most once and
   cannot cycle, so WB_BOUNDED_REWRITE_CONV ths k repeats such passes only
   while the term keeps changing, and at most k times.

   wb_tail_rewrite_asms selects the assumptions a composed tail's goal can use.
   That goal mentions only the freshly generalized final state and the event
   list, so only three kinds of assumption can contribute: variable definitions
   (the stripped `e2 = f_events ...`), reads of a state the goal still
   mentions, and the `val (word ...)` size facts the enclosing spec's buffer
   bounds are phrased over.  The rest are dropped, not discharged. ---- *)
let WB_BOUNDED_REWRITE_CONV ths k tm =
  let conv = GEN_REWRITE_CONV ONCE_DEPTH_CONV ths in
  let rec go k tm =
    if k <= 0 then REFL tm else
    let th = try conv tm with Failure _ -> REFL tm in
    let tm' = rhs(concl th) in
    if tm' = tm then th else TRANS th (go (k-1) tm') in
  go k tm;;

let wb_tail_rewrite_asms (asl,w) =
  let gvars = frees w in
  let usable th =
    let c = concl th in
    is_eq c &&
    (let l = lhs c in
     is_var l ||
     (match strip_comb l with
      | Const("read",_), [_; st] -> mem st gvars
      | Const("val",_), _ -> true
      | _ -> false)) in
  map snd (filter (usable o snd) asl);;

(* Targeted stand-in for the blanket ASM_REWRITE_TAC[] at the head of a
   composed tail's post-tactic, which overflows on the 9..16 and >=17 legs
   (unlike the 5..8 legs, whose tail starts at s0); ASM_SIMP_TAC is no better,
   having the same assumption set and the same net.  The trailing REWRITE_TAC[]
   closes the trivial conjuncts a blanket call would. *)
let WB_TAIL_POST_ASM_REWRITE_TAC : tactic = fun (asl,w) ->
  (CONV_TAC (WB_BOUNDED_REWRITE_CONV (wb_tail_rewrite_asms (asl,w)) 12) THEN
   REWRITE_TAC[]) (asl,w);;

(* After MEMACCESS_INBOUNDS_APPEND splits the trace, the first conjunct is the
   reusable tail theorem's own `memaccess_inbounds` postcondition, which is
   already an assumption, so it needs matching, not search.  A blanket
   ASM_MESON_TAC[] is handed every assumption instead and diverges on the 9..16
   and >=17 legs.  Trying the two assumption-matching tactics first closes that
   case at once and never reaches MESON.  The fallback is the unrestricted
   ASM_MESON_TAC[]: on the 5..8 legs this conjunct needs facts beyond the
   inbounds assumptions.

   Plain matching is still not enough on the 9..16 and >=17 legs, because the
   two sides spell the same buffer bound differently.  mk_tail_safe_goal states
   the tail's postcondition over `val (word (128 * nblk):int64) DIV 8 * 1`, and
   prove_tail_safe SUBST_ALL_TACs that to `16 * nblk` only inside its own
   proof, so the exported theorem keeps the `val` spelling.  The enclosing band
   closers then run `RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV)` and
   `CONV_TAC NUM_REDUCE_CONV` over a leg where nblk is already a numeral, which
   collapses one side to a literal (`144` at band 9) while the other keeps the
   `val (word ...) DIV 8 * 1` form.  The 5..8 legs never diverge this way
   because they specialize the tail at s0 with no intervening reduction.  So
   normalize both sides to the same spelling and try the match again;
   equality-shaped goals and the legs the plain matches close are untouched,
   because the plain matches are tried first.

   The decisive normalizer is APPEND_NIL.  Both sides carry the tail's selector
   `(@f_events. ...) in_p key_p ... stackpointer`, the goal's copy inside a
   `memaccess_inbounds` argument, the assumption's as the `e2 = ...`
   definition.  But RESHAPE_LOOP_TAC leaves the goal's copy with
   `APPEND (APPEND [...] []) []` wrappers around the range lists inside the
   epsilon's body, where the assumption's copy has the bare lists.  Two epsilon
   terms whose bodies differ at all are different terms, so `e2` never rewrites
   and the conjunct cannot match however the bounds are spelled.  APPEND_NIL
   collapses the wrappers and the two selectors become alpha-equal.

   WB_SAFETY_BYTES_LEN and the `val` size facts also reconcile the buffer
   bounds, spelled `val (word 1152) DIV 8 * 1` in the assumption against the
   literal `144` in the goal.  WB_SAFETY_BYTES_LEN is the rule prove_tail_safe
   itself uses for this bound; it matters on the >=17 leg, where nblk stays
   symbolic and the `val` facts alone would leave `(128 * nblk) DIV 8 * 1`
   needing symbolic arithmetic that neither NUM_REDUCE nor MESON closes. *)
let WB_TAIL_EVENTS_DISCHARGE_TAC : tactic = fun (asl,w) ->
  let bytelen =
    mapfilter (fun (_,th) -> MATCH_MP WB_SAFETY_BYTES_LEN th) asl in
  let valfacts = map snd (filter (fun (_,th) ->
      let c = concl th in
      is_eq c &&
      (match strip_comb(lhs c) with
       | Const("val",_),_ -> true
       (* the stripped `e2 = f_events ...` definition.  Without it the
          assumption keeps the bare variable `e2` where the goal has the
          selector it stands for, so the two can never converge, however the
          rest is normalized. *)
       | _ -> is_var(lhs c))) asl) in
  (* WB_SAFETY_BYTES_LEN_NOVAL is unconditional, so it is prepended rather than
     derived from an assumption: on the >=17 leg the goal's bound has already
     lost its `val (word ...)` wrapper, so WB_SAFETY_BYTES_LEN cannot reach it
     (see that lemma's comment). *)
  let rules = WB_SAFETY_BYTES_LEN_NOVAL :: bytelen @ valfacts in
  (* APPEND_NIL gets a full TOP_DEPTH traversal: the wrappers are nested two
     deep (`APPEND (APPEND l []) []`) and a single ONCE_DEPTH pass strips only
     the outer one.  This cannot cycle, because the right side of APPEND_NIL is
     a strict subterm.  The assumption-derived rules get the bounded passes of
     WB_BOUNDED_REWRITE_CONV instead: TOP_DEPTH would diverge on the cyclic
     pairs described there, and a single ONCE_DEPTH pass does not reach the
     bounds, which sit inside the epsilon's body below the first redex.

     The APPEND_NIL pass runs both before and after the rule expansion.  The
     goal's wrappers are there from the start, but on the assumption side the
     trace is still the bare variable `e2`, and its wrappers only appear once
     the `e2 = <selector>` definition has been rewritten in.  With the leading
     pass alone the two sides would end as epsilon terms whose bodies differ by
     `APPEND (APPEND [...] []) []`, and the goal would fall through to the
     diverging ASM_MESON_TAC[].  On the 5..8 and 9..16 legs nblk is a numeral,
     their bounds have already converged, and the trailing pass changes
     nothing. *)
  let append_nil_pass = TRY_CONV(GEN_REWRITE_CONV TOP_DEPTH_CONV [APPEND_NIL]) in
  let nconv =
    append_nil_pass THENC
    (if rules = [] then ALL_CONV else WB_BOUNDED_REWRITE_CONV rules 12) THENC
    append_nil_pass THENC
    TRY_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV) in
  let match_with f =
    FIRST_ASSUM (fun th -> ACCEPT_TAC(f th)) ORELSE
    FIRST_ASSUM (fun th -> MATCH_ACCEPT_TAC(f th)) in
  (match_with I ORELSE
   match_with (CONV_RULE nconv) ORELSE
   (CONV_TAC nconv THEN (match_with I ORELSE match_with (CONV_RULE nconv))) ORELSE
   ASM_MESON_TAC[]) (asl,w);;

(* Local, net-safe shadow of the stock DISCHARGE_MEMACCESS_INBOUNDS_TAC
   (common/consttime.ml), for the second conjunct below.

   The stock tactic overflows the stack ("looping recursion?") on the 9..16 and
   >=17 legs.  Its one blanket call is the ASM_REWRITE_TAC[] inside
   DISCHARGE_MEMACCESS_INBOUNDS_USING_ASM_TAC, whose job is only to expand the
   stripped `e2 = f_events ...` definition so that the undischarged assumption
   and the goal take the same shape.  It is the failure mode described at
   WB_BOUNDED_REWRITE_CONV, and the remedy is the same: bound the traversal
   rather than narrow the fact set (the overflow needs the cycle to be
   reachable from the goal).

   On the shapes the stock tactic does close (identical-term match, range
   widening, concrete goal, and APPEND-split with and without `e2` defined) the
   shadow agrees with it exactly, so the 5..8 legs take the same path.

   The code is the stock tactic apart from that one call, a recursion cap on
   main_tac, which turns a non-shrinking trace into a Failure the enclosing
   ORELSE can act on instead of an exhausted OCaml stack, and the two dispatch
   cases described below.

   The bounded traversal is made of the same single ONCE_DEPTH passes as
   WB_BOUNDED_REWRITE_CONV, repeated because the shapes needing normalization
   sit below the first redex, inside the tail selector's epsilon body.  But
   here the repetition stops when a term repeats, not only when it stops
   changing: an oscillating equation pair flips the term on every pass, so a
   stabilization test alone never fires and the conjunct is left unprovable. *)
let WB_BOUNDED_ASM_REWRITE_TAC (extra:thm list) : tactic = fun (asl,w) ->
  let rules = extra @ wb_tail_rewrite_asms (asl,w) in
  let conv = GEN_REWRITE_CONV ONCE_DEPTH_CONV rules in
  let rec go seen k tm =
    if k <= 0 then REFL tm else
    let th = try conv tm with Failure _ -> REFL tm in
    let tm' = rhs(concl th) in
    if tm' = tm || exists (fun t -> t = tm') seen then REFL tm
    else TRANS th (go (tm::seen) (k-1) tm') in
  (CONV_TAC (go [] 12) THEN REWRITE_TAC extra) (asl,w);;

let WB_DISCHARGE_MEMACCESS_INBOUNDS_USING_ASM_TAC:tactic =
  let try_discharge (meminb_th:thm):tactic =
    UNDISCH_TAC (concl meminb_th) THEN
    WB_BOUNDED_ASM_REWRITE_TAC [] THEN
    REWRITE_TAC[APPEND;APPEND_NIL] THEN
    ((MATCH_MP_TAC MEMACCESS_INBOUNDS_MEM THEN
      REWRITE_TAC[ALL;MEM] THEN NO_TAC) ORELSE
     (MATCH_MP_TAC MEMACCESS_INBOUNDS_CONTAINED THEN
      DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC THEN NO_TAC)) in
  W (fun (asl,w) ->
    let meminbounds = map snd (filter (fun (_,th) ->
          let cth = concl th in
          is_comb cth &&
          name_of (fst (strip_comb cth)) = "memaccess_inbounds") asl) in
    if meminbounds = [] then
      failwith "No memaccess_inbounds assumption" else
    end_itlist (fun tac1 tac2 -> tac1 ORELSE tac2)
      (map try_discharge meminbounds));;

let WB_DISCHARGE_MEMACCESS_INBOUNDS_TAC =
  let append_nil_th =
      MESON[APPEND]
        `memaccess_inbounds (APPEND [] b) = memaccess_inbounds b /\
         memaccess_inbounds (APPEND (APPEND [] []) b) = memaccess_inbounds b` in
  let rec main_tac d (asl,w) =
    if d <= 0 then failwith "WB_DISCHARGE_MEMACCESS_INBOUNDS_TAC: depth" else
    ((WB_DISCHARGE_MEMACCESS_INBOUNDS_USING_ASM_TAC) ORELSE

    (DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC THEN NO_TAC) ORELSE

    (REWRITE_TAC[CONJUNCT2 APPEND] THEN
      CONV_TAC ((RATOR_CONV o RATOR_CONV o RAND_CONV) CONS_TO_APPEND_CONV) THEN
      GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_APPEND] THEN
      CONJ_TAC THENL [
        DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC THEN NO_TAC;
        REWRITE_TAC[append_nil_th] THEN main_tac (d-1) THEN NO_TAC
      ]) ORELSE

    (GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_APPEND] THEN
      CONJ_TAC THENL [
        main_tac (d-1) THEN NO_TAC;
        DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC THEN NO_TAC;
      ]) ORELSE

    (GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_APPEND] THEN
      CONJ_TAC THENL [
        WB_DISCHARGE_MEMACCESS_INBOUNDS_USING_ASM_TAC;
        main_tac (d-1);
      ] THEN NO_TAC)) (asl,w)
  in
  (* Two dispatch cases main_tac does not have, both reached only by the >=17
     leg and no-ops on every shape the 5..8 and 9..16 legs present.

     (1) REPEAT CONJ_TAC.  main_tac dispatches on `memaccess_inbounds` heads
     and on MEMACCESS_INBOUNDS_APPEND, so a top-level `/\` matches nothing at
     all and the whole tactic reports "could not identify the pattern".  The
     >=17 leg gets one because its scaffold entry is
     `APPEND residue (APPEND (ENUMERATEL ..) front)`:
     DISCHARGE_WB_COMPOSED_TAIL_TAC's REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND]
     then distributes all the way down and hands this call a five-way
     conjunction.  The bands 9..16 enter the scaffold at a bare f_ev_k with no
     APPEND, so their goal stays a single memaccess_inbounds term and REPEAT
     CONJ_TAC is a no-op there.

     (2) The ENUMERATEL rule.  Of those five conjuncts four are concrete traces
     that main_tac already closes; the fifth is the symbolic loop trace, and it
     needs the quantified-i step before the per-iteration body, which main_tac
     then closes by its ordinary assumption route, since the body's stores are
     already covered by the tail theorem's own inbounds assumption. *)
  let close_one =
    main_tac 8 ORELSE
    (MATCH_MP_TAC MEMACCESS_INBOUNDS_ENUMERATEL THEN
     GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN main_tac 8) ORELSE
    FAIL_TAC
      "WB_DISCHARGE_MEMACCESS_INBOUNDS_TAC could not identify the pattern" in
  REWRITE_TAC[CONJUNCT1 APPEND; APPEND_NIL] THEN
  REPEAT CONJ_TAC THEN close_one;;

let DISCHARGE_WB_COMPOSED_TAIL_TAC =
  WB_SAFETY_PROPERTY_TAC
   (REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN
    CONJ_TAC THENL
     [WB_TAIL_EVENTS_DISCHARGE_TAC;
      WB_DISCHARGE_MEMACCESS_INBOUNDS_TAC]);;


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

(* ---- the event-trace scaffold of the core, one branch per leg.  On the >=17
   leg the trace is already in ENSURES_EVENTS_WHILE_UP2 shape,
     e2 = APPEND <residue ladder>
                 (APPEND (ENUMERATEL ((nblk-9) DIV 8) f_ev_loop) f_ev_front),
   so the residue ladder lands in the rule's discarded e_back.  The ladder has
   its own metavariable for each of the eight values of (nblk-9) MOD 8: HOL
   metavariables are shared across the goal stack, so a single shared one would
   be fixed by whichever residue closed first. ---- *)

let core_scaffold =
 `\(in_p:int64) (key_p:int64) (htbl_p:int64) (out_p:int64) (xi_p:int64)
   (ivec_p:int64) (nblk:num) (pc:num) (stackpointer:int64).
     if nblk = 1 then f_ev_1 in_p key_p htbl_p out_p xi_p ivec_p nblk pc stackpointer
     else if nblk = 2 then f_ev_2 in_p key_p htbl_p out_p xi_p ivec_p nblk pc stackpointer
     else if nblk = 3 then f_ev_3 in_p key_p htbl_p out_p xi_p ivec_p nblk pc stackpointer
     else if nblk = 4 then f_ev_4 in_p key_p htbl_p out_p xi_p ivec_p nblk pc stackpointer
     else if nblk <= 8 then
       APPEND
         ((if nblk = 5 then f_ev_5
           else if nblk = 6 then f_ev_6
           else if nblk = 7 then f_ev_7
           else f_ev_8) in_p key_p htbl_p out_p xi_p ivec_p nblk pc stackpointer)
         (f_ev_58_front in_p key_p htbl_p out_p xi_p ivec_p nblk pc stackpointer)
     else if nblk = 9 then f_ev_9 in_p key_p htbl_p out_p xi_p ivec_p nblk pc stackpointer
     else if nblk = 10 then f_ev_10 in_p key_p htbl_p out_p xi_p ivec_p nblk pc stackpointer
     else if nblk = 11 then f_ev_11 in_p key_p htbl_p out_p xi_p ivec_p nblk pc stackpointer
     else if nblk = 12 then f_ev_12 in_p key_p htbl_p out_p xi_p ivec_p nblk pc stackpointer
     else if nblk = 13 then f_ev_13 in_p key_p htbl_p out_p xi_p ivec_p nblk pc stackpointer
     else if nblk = 14 then f_ev_14 in_p key_p htbl_p out_p xi_p ivec_p nblk pc stackpointer
     else if nblk = 15 then f_ev_15 in_p key_p htbl_p out_p xi_p ivec_p nblk pc stackpointer
     else if nblk = 16 then f_ev_16 in_p key_p htbl_p out_p xi_p ivec_p nblk pc stackpointer
     else
       APPEND
         ((if (nblk - 9) MOD 8 = 0 then f_ev_t0
           else if (nblk - 9) MOD 8 = 1 then f_ev_t1
           else if (nblk - 9) MOD 8 = 2 then f_ev_t2
           else if (nblk - 9) MOD 8 = 3 then f_ev_t3
           else if (nblk - 9) MOD 8 = 4 then f_ev_t4
           else if (nblk - 9) MOD 8 = 5 then f_ev_t5
           else if (nblk - 9) MOD 8 = 6 then f_ev_t6
           else f_ev_t7) in_p key_p htbl_p out_p xi_p ivec_p nblk pc stackpointer)
         (APPEND
           (ENUMERATEL ((nblk - 9) DIV 8)
             (\i. f_ev_loop in_p key_p htbl_p out_p xi_p ivec_p nblk pc stackpointer i))
           (f_ev_front in_p key_p htbl_p out_p xi_p ivec_p nblk pc stackpointer))
     :(uarch_event)list`;;

(* ---- >=17 entry prep: establish the bounds and collapse the 16-way ladder to
   its else-branch.  The rewrite discharges each `~(nblk = k)` from the
   `17 <= nblk` already present and leaves no hypotheses behind; sixteen
   asserted `~(nblk = k)` hypotheses would instead be walked at every
   simulation step and again by DISCHARGE_SAFETY_PROPERTY_TAC over the whole
   trace. ---- *)
let GE17_LADDER_KILL_TAC : tactic = fun (asl,w) ->
  let neq = map (fun k ->
    EQF_INTRO (UNDISCH (ARITH_RULE
      (mk_imp(`17 <= nblk`, mk_neg(mk_eq(`nblk:num`, mk_small_numeral k))))))) (1--16) in
  let nle8 = EQF_INTRO
    (UNDISCH (ARITH_RULE `17 <= nblk ==> ~(nblk <= 8)`)) in
  (GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV)
      (COND_CLAUSES::nle8::neq) THEN
   REWRITE_TAC (nle8::neq)) (asl,w);;

let GE17_PREP_TAC =
  SUBGOAL_THEN `17 <= nblk /\ 9 <= nblk` STRIP_ASSUME_TAC THENL
   [MP_TAC(ASSUME `~(nblk <= 16)`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC; ALL_TAC] THEN
  GE17_LADDER_KILL_TAC;;

(* ---- reshape the collapsed trace for SEQUENCE:
     APPEND ladder (APPEND loop front)
       -> APPEND (APPEND ladder (APPEND loop [])) front,
   so that SEQUENCE at the loop head peels `e_front_tail = front` and
   `e_back = APPEND ladder (APPEND loop [])`.  ONCE_REWRITE_TAC is used because
   GEN_REWRITE_TAC with a RAND o ONCE_DEPTH path does not reach the intended
   APPEND occurrence. ---- *)
let RESHAPE_LOOP_TAC : tactic = fun (asl,w) ->
  let e2var = `e2:(uarch_event)list` in
  let e2eq = find_term (fun t -> is_eq t && lhs t = e2var
                 && (match rhs t with Comb(Comb(Const("APPEND",_),_),_) -> true | _ -> false)) w in
  let rhs_e2 = rhs e2eq in
  let a,bb,c = (match rhs_e2 with
     | Comb(Comb(Const("APPEND",_),a),Comb(Comb(Const("APPEND",_),bb),c)) -> a,bb,c
     | _ -> failwith "RESHAPE_LOOP_TAC: unexpected e2 shape") in
  let nil = `[]:(uarch_event)list` in
  let ap x y = mk_binop `APPEND:(uarch_event)list->(uarch_event)list->(uarch_event)list` x y in
  let reshaped = ap (ap a (ap bb nil)) c in
  let reshape_thm = prove(mk_eq(rhs_e2, reshaped), REWRITE_TAC[APPEND_NIL; APPEND_ASSOC]) in
  ONCE_REWRITE_TAC[reshape_thm] (asl,w);;

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
     read X6 s = htbl_p /\
     read X3 s = xi_p /\
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
     read X3 s = xi_p /\
     read X4 s = word_add in_p (word (16 * nblk)) /\
     read X5 s = word (16 * nblk) /\
     read X6 s = htbl_p /\
     read X9 s = word (16 * nblk) /\
     read X10 s = word_add stackpointer (word 64) /\
     read X11 s = key_p /\
     read X16 s = ivec_p`;;

(* Collapse the first four concrete leaves of core_scaffold and expose the
   APPEND shared by the bands 5..8 without first making nblk concrete. *)
let LE8_58_LADDER_OPEN_TAC : tactic = fun (asl,w) ->
  let neq = map (fun k ->
    EQF_INTRO (UNDISCH (ARITH_RULE
      (mk_imp(`5 <= nblk`, mk_neg(mk_eq(`nblk:num`, mk_small_numeral k))))))) (1--4) in
  (GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV)
      (COND_CLAUSES::(ASSUME `nblk <= 8`)::neq) THEN
   REWRITE_TAC neq) (asl,w);;

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
   then the rest (loop and tail, pc+1212 to pc+4556). ---- *)
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
     read X6 s = htbl_p /\
     read X3 s = xi_p /\
     read X11 s = key_p`;;

(* ---- the main loop, on the rest subgoal (pc+1212 to pc+4556) once the front
   leg is closed: ENSURES_EVENTS_WHILE_UP2_TAC then REPEAT CONJ_TAC leave four
   subgoals, in this order:
     G0 the count is nonzero, ~((nblk-9) DIV 8 = 0)
     G1 entry (i = 0) at pc+1212: the invariant at 0
     G2 the loop body, for all i
     G3 exit and tail, pc+2572 to pc+4556 (the residue dispatch) ---- *)
let GE17_LOOP_OPEN_TAC =
  ENSURES_EVENTS_WHILE_UP2_TAC `(nblk - 9) DIV 8` `pc + 0x4bc` `pc + 0xa0c` loop_inv THEN
  REPEAT CONJ_TAC;;

(* G0: the count is nonzero *)
let GE17_COUNT_TAC =
  MP_TAC(ASSUME `17 <= nblk`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  SIMP_TAC[DIV_EQ_0; ARITH_EQ] THEN ARITH_TAC;;

(* G1, entry (i = 0): the precondition is the postcondition after normalizing
   0+1, 128*1, ENUMERATEL 0, APPEND [] and *1 *)
let GE17_ENTRY_TAC =
  ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[ENUMERATEL; APPEND; ADD_CLAUSES; MULT_CLAUSES] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_exists (concl th))) THEN
  ASM_REWRITE_TAC[MULT_CLAUSES];;

(* G2, the loop body.  STRIP_EXISTS_ASSUM_TAC after ENSURES_INIT_TAC is
   required, not cosmetic: the invariant carries an accumulated
   `exists e2. read events s0 = APPEND e2 e /\ ...`, and unless it is stripped,
   `read events s0` is never exposed and the closing EXISTS_E2_TAC fails in
   AP_THM_TAC.  This mirrors what bignum_copy_row_from_table_8n.ml gets from
   ARM_SIM_TAC's ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC).  WBN_PC_BRIDGE
   already has i free, so it is MP'd rather than SPEC'd. *)
let ptrcmp_i = SPECL [`in_p:int64`; `128 * (i + 2)`; `128 * ((nblk - 1) DIV 8)`] WB_PTRCMP_FLAGS;;
let x0norm_i = WORD_RULE
  `word_add (word_add in_p (word (128 * (i + 1)))) (word 128):int64 = word_add in_p (word (128 * (i + 2)))`;;
let pcbridge_i = MP WBN_PC_BRIDGE (ASSUME `9 <= nblk`);;

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

(* ---- G3, the exit and tail leg, pc+2572 to pc+4556: the straight-line
   prepretail to pc+3812, then the 8-way dispatch on the leftover block count
   (nblk-9) MOD 8. ---- *)

(* the leftover-byte count in X5 at the tail compare, under 17 <= nblk and the
   pointer bound *)
let TAIL_LEFTOVER_BYTES = prove
  (`17 <= nblk /\ val (in_p:int64) + 16 * nblk < 2 EXP 63
     ==> word_sub (word_add in_p (word (16 * nblk)))
                  (word_add in_p (word (128 * ((nblk - 9) DIV 8 + 1))))
         = word (16 * ((nblk - 9) MOD 8 + 1)):int64`,
   STRIP_TAC THEN
   SUBGOAL_THEN `16 * nblk = 128 * ((nblk - 9) DIV 8 + 1) + 16 * ((nblk - 9) MOD 8 + 1)` ASSUME_TAC THENL
    [MP_TAC(SPECL [`nblk - 9`; `8`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
     MP_TAC(ASSUME `17 <= nblk`) THEN ARITH_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE);;

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

(* ---- the core safety opening.  Unlike a `\s s'. true` frame, this one
   unfolds MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI up front so that
   ENSURES_FINAL_STATE_TAC can discharge the real frame at every leaf; the
   wrapper needs the real frame, because it simulates the epilogue after the
   core big-step and so needs aligned_bytes_loaded preserved across it.
   Mirrors BIGNUM_INV_P25519_SAFE. ---- *)
let CORE_SAFE_OPEN_TAC =
  CONCRETIZE_F_EVENTS_TAC core_scaffold THEN REPEAT META_EXISTS_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
  REPEAT STRIP_TAC THEN
  VAL_INT64_TAC `16 * nblk` THEN VAL_INT64_TAC `128 * nblk`;;

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

(* ---- the ABI wrapper.  The stock ARM_ADD_RETURN_STACK_TAC is not used: the
   exported spec quantifies over the C argument bit_len, while the core below
   takes word (128 * nblk) with 1 <= nblk, and the prologue contains the entry
   guard, whose zero and non-multiple-of-128 branches return before the core.
   So the crossing is hand-rolled (ARBITRARY_WRAPPER_SAFE_TAC below). ---- *)

let WB_GUARD_FALLTHROUGH_TAC =
  SUBGOAL_THEN `val (word (128 * nblk):int64) = 128 * nblk` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(128 * nblk = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (word_and (word (128 * nblk):int64) (word 127)) = 0` ASSUME_TAC THENL
   [SUBGOAL_THEN `(127:num) = 2 EXP 7 - 1` SUBST1_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(2:num) EXP 7 = 128` SUBST1_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    REWRITE_TAC[MOD_MULT]; ALL_TAC];;

(* ---- the core safety theorem, over the real MAYCHANGE frame the wrapper
   needs.  Its memaccess bounds are the assembly's exact footprint.  The public
   theorem below takes its bounds from the C signature through mk_safety_spec:
   the tag and ivec (16), key (240) and htable (192) bounds and the 80-byte
   frame equal this footprint, while the in/out bounds are the C length
   len_bits/8 (val bit_len DIV 8 bytes), which contains the 16 * nblk footprint
   and equals it when bit_len = word (128 * nblk). ---- *)
let AES256_GCM_DEC_ALT_SAFE = prove
 (`exists f_events.
     forall e pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p nblk.
         1 <= nblk /\
         128 * nblk < 2 EXP 64 /\
         val in_p + 16 * nblk < 2 EXP 63 /\
         aligned 16 stackpointer /\
         ALLPAIRS nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16]
         [word pc,LENGTH aes256_gcm_dec_alt_tmc; in_p,16 * nblk;
          key_p,240; htbl_p,192; stackpointer,80] /\
         PAIRWISE nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16] /\
         ALL (nonoverlapping (stackpointer,80))
         [word pc,LENGTH aes256_gcm_dec_alt_tmc; in_p,16 * nblk;
          key_p,240; htbl_p,192]
         ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_alt_tmc /\
                  read PC s = word (pc + 28) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS
                  [in_p; word (128 * nblk); out_p; xi_p; ivec_p; key_p; htbl_p]
                  s /\
                  read events s = e)
             (\s. read PC s = word (pc + 4556) /\
                  (exists e2.
                       read events s = APPEND e2 e /\
                       e2 =
                       f_events in_p key_p htbl_p out_p xi_p ivec_p nblk pc
                       stackpointer /\
                       memaccess_inbounds e2
                       [in_p,16 * nblk; xi_p,16; ivec_p,16;
                        key_p,240; htbl_p,192; out_p,16 * nblk;
                        stackpointer,80]
                       [out_p,16 * nblk; xi_p,16; ivec_p,16;
                        stackpointer,80]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
              [memory :> bytes (out_p,16 * nblk); memory :> bytes (xi_p,16);
               memory :> bytes (ivec_p,16);
               memory :> bytes (word_add stackpointer (word 64),16)] ,,
              MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15])`,
  PURE_REWRITE_TAC[GSYM WB_CORE_FRAME_EQ] THEN CORE_SAFE_TAC);;

(* The wrapper's f_events gets an explicit three-path witness rather than
   CONCRETIZE_F_EVENTS_TAC and UNIFY_REFL_TAC.  The latter leave the core's
   X_CHOOSE'd f_events_callee variable in the witness, which then escapes its
   scope and makes the CHOOSE fail at extraction.

   The public witness dispatches only on the public bit_len:
   - invalid non-multiple: the three reject-path jumps;
   - zero: the cbz/return jumps;
   - valid nonzero: prologue stores/jumps, the core trace, and epilogue
     loads/return.

   f_events_core is a placeholder for the core's trace; the only part that
   cannot be written down is which variable holds it, since
   ASSUME_CALLEE_SAFETY_TAILED_TAC chooses that variable itself. *)
let wrapper_witness_template =
 `\(in_p:int64) (key_p:int64) (htbl_p:int64) (out_p:int64) (xi_p:int64)
   (ivec_p:int64) (bit_len:int64) (pc:num) (sp:int64) (ra:int64).
     if val bit_len MOD 128 = 0 then
       if val bit_len = 0 then
         [EventJump (word (pc + 5952),ra);
          EventJump (word pc,word (pc + 5948))]
       else
         APPEND
           [EventJump (word (pc + 4576),ra); EventLoad (sp,16);
            EventLoad (word_add sp (word 48),16);
            EventLoad (word_add sp (word 32),16);
            EventLoad (word_add sp (word 16),16)]
           (APPEND
             (f_events_core in_p key_p htbl_p out_p xi_p ivec_p
               (gcm_wb_blocks bit_len) pc sp)
             [EventStore (word_add sp (word 48),16);
              EventStore (word_add sp (word 32),16);
              EventStore (word_add sp (word 16),16); EventStore (sp,16);
              EventJump (word (pc + 8),word (pc + 12));
              EventJump (word pc,word (pc + 4))])
     else
       [EventJump (word (pc + 5952),ra);
        EventJump (word (pc + 8),word (pc + 5948));
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
  ABBREV_TAC `nblk = gcm_wb_blocks bit_len` THEN
  ASM_CASES_TAC `val(bit_len:int64) MOD 128 = 0` THENL
   [ALL_TAC;
    (* Invalid non-multiple: reject before any memory access. *)
    SUBGOAL_THEN `nblk = 0` SUBST_ALL_TAC THENL
     [EXPAND_TAC "nblk" THEN REWRITE_TAC[gcm_wb_blocks] THEN
      ASM_REWRITE_TAC[COND_CLAUSES];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(val(bit_len:int64) = 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `~(val(bit_len:int64) MOD 128 = 0)` THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `~(val(word_and (bit_len:int64) (word 127)) = 0)`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `127 = 2 EXP 7 - 1` SUBST1_TAC THENL
       [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
      REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
      ASM_REWRITE_TAC[ARITH_RULE `2 EXP 7 = 128`];
      ALL_TAC] THEN
    WB_GUARD_RETURN_TAC 5
      (REWRITE_TAC[APPEND;memaccess_inbounds;ALL;EX;FST;SND])] THEN
  ASM_CASES_TAC `val(bit_len:int64) = 0` THENL
   [(* Zero: cbz returns before the stack saves. *)
    SUBGOAL_THEN `nblk = 0` SUBST_ALL_TAC THENL
     [EXPAND_TAC "nblk" THEN REWRITE_TAC[gcm_wb_blocks] THEN
      ASM_REWRITE_TAC[COND_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    SUBGOAL_THEN `bit_len:int64 = word 0` SUBST_ALL_TAC THENL
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
    MP_TAC(SPECL [`val(bit_len:int64)`; `128`]
      (CONJUNCT2 DIVISION_SIMP)) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(bit_len:int64) = 128 * nblk` ASSUME_TAC THENL
   [EXPAND_TAC "nblk" THEN ASM_SIMP_TAC[GCM_WB_BLOCKS_VALID];
    ALL_TAC] THEN
  SUBGOAL_THEN `128 * nblk < 2 EXP 64` ASSUME_TAC THENL
   [MP_TAC(ISPEC `bit_len:int64` VAL_BOUND_64) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `bit_len:int64 = word (128 * nblk)` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if concl th = `val(bit_len:int64) = 128 * nblk`
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
        `in_p:int64`;`out_p:int64`;`xi_p:int64`;`ivec_p:int64`;
        `key_p:int64`;`htbl_p:int64`;`nblk:num`;pd] cth))) THEN
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

(* The statement of the exported safety theorem, for an arbitrary bit_len,
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
     forall e pc stackpointer in_p bit_len out_p xi_p ivec_p key_p htbl_p
            returnaddress.
         val in_p + 16 * gcm_wb_blocks bit_len < 2 EXP 63 /\
         aligned 16 stackpointer /\
         ALLPAIRS nonoverlapping
         [out_p,16 * gcm_wb_blocks bit_len; xi_p,16; ivec_p,16]
         [word pc,LENGTH aes256_gcm_dec_alt_tmc;
          in_p,16 * gcm_wb_blocks bit_len; key_p,240; htbl_p,192;
          word_sub stackpointer (word 80),80] /\
         PAIRWISE nonoverlapping
         [out_p,16 * gcm_wb_blocks bit_len; xi_p,16; ivec_p,16] /\
         ALL (nonoverlapping (word_sub stackpointer (word 80),80))
         [word pc,LENGTH aes256_gcm_dec_alt_tmc;
          in_p,16 * gcm_wb_blocks bit_len; key_p,240; htbl_p,192]
         ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    aes256_gcm_dec_alt_tmc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS
                  [in_p; bit_len; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                       read events s = APPEND e2 e /\
                       e2 =
                       f_events in_p key_p htbl_p out_p xi_p ivec_p bit_len pc
                         (word_sub stackpointer (word 80)) returnaddress /\
                       memaccess_inbounds e2
                       [in_p,val bit_len DIV 8 * 1; xi_p,16; ivec_p,16;
                        key_p,240; htbl_p,192; out_p,val bit_len DIV 8 * 1;
                        word_sub stackpointer (word 80),80]
                       [out_p,val bit_len DIV 8 * 1; xi_p,16; ivec_p,16;
                        word_sub stackpointer (word 80),80]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
              [memory :> bytes (out_p,16 * gcm_wb_blocks bit_len);
               memory :> bytes (xi_p,16);
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
     forall e pc stackpointer in_p bit_len out_p xi_p ivec_p key_p htbl_p
            returnaddress.
         val in_p + 16 * gcm_wb_blocks bit_len < 2 EXP 63 /\
         aligned 16 stackpointer /\
         ALLPAIRS nonoverlapping
         [out_p,16 * gcm_wb_blocks bit_len; xi_p,16; ivec_p,16]
         [word pc,LENGTH aes256_gcm_dec_alt_mc;
          in_p,16 * gcm_wb_blocks bit_len; key_p,240; htbl_p,192;
          word_sub stackpointer (word 80),80] /\
         PAIRWISE nonoverlapping
         [out_p,16 * gcm_wb_blocks bit_len; xi_p,16; ivec_p,16] /\
         ALL (nonoverlapping (word_sub stackpointer (word 80),80))
         [word pc,LENGTH aes256_gcm_dec_alt_mc;
          in_p,16 * gcm_wb_blocks bit_len; key_p,240; htbl_p,192]
         ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    aes256_gcm_dec_alt_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS
                  [in_p; bit_len; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                       read events s = APPEND e2 e /\
                       e2 =
                       f_events in_p key_p htbl_p out_p xi_p ivec_p bit_len pc
                         (word_sub stackpointer (word 80)) returnaddress /\
                       memaccess_inbounds e2
                       [in_p,val bit_len DIV 8 * 1; xi_p,16; ivec_p,16;
                        key_p,240; htbl_p,192; out_p,val bit_len DIV 8 * 1;
                        word_sub stackpointer (word 80),80]
                       [out_p,val bit_len DIV 8 * 1; xi_p,16; ivec_p,16;
                        word_sub stackpointer (word 80),80]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
              [memory :> bytes (out_p,16 * gcm_wb_blocks bit_len);
               memory :> bytes (xi_p,16);
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
