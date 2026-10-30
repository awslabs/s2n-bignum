(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================== *)
(* AES-128-GCM decryption of whole blocks, 8 blocks at a time.                *)
(*                                                                            *)
(* The <=8-block chain proves the kernel for nblk <= 8 blocks; the nblk > 8   *)
(* proof extends it to the software-pipelined 8-blocks-per-iteration main     *)
(* loop L128_dec_main_loop (0x3b4..0x7f8), the GHASH catch-up prepretail      *)
(* (0x7fc..0xbc0), and the tail cascade (from 0xbc4), so correctness holds    *)
(* for arbitrary nblk >= 1.                                                   *)
(*                                                                            *)
(* Binary: arm/aes_gcm/aes128_gcm_dec_alt.o                                   *)
(*                                                                            *)
(* KEY PIPELINE FACT:                                                         *)
(*         GHASH lags stores by one 8-block group, so the ENSURES_WHILE       *)
(*         invariant is the TWO-STREAM form (store/counter stream at 8(i+1),  *)
(*         GHASH stream at 8i, bridged by raw ciphertext regs q8..q15), NOT   *)
(*         a lag-free single fold.                                            *)
(*                                                                            *)
(* The kernel is the AES-128 counterpart of aes256_gcm_dec_alt, and this      *)
(* proof follows arm/proofs/aes256_gcm_dec_alt.ml step for step, with the     *)
(* ten-round keystream tower aes9, the eleven round keys and AWS-LC's         *)
(* AES-128 instruction schedule.  The file holds, in order:                   *)
(*   - the Htable known-answer instances at two AES-128 keys;                 *)
(*   - the proof's own copy of the binary-independent layer of                *)
(*     aes256_gcm_dec_alt.ml: the GHASH/Karatsuba bridge and SIMD-fold        *)
(*     stepping layer, the counter core and the decrypt specifications;       *)
(*   - the AES-128 vocabulary: aes9, aes128_encrypt and the CTR output        *)
(*     specification gcm_dec128_pt_bytes;                                     *)
(*   - the machine code, the shared front, the band tails, the small-message  *)
(*     path (nblk <= 4) and the readable band and dispatch theorems;          *)
(*   - the nblk > 8 proof: the front-N, the ENSURES_WHILE loop, the           *)
(*     prepretail and the recomposition;                                      *)
(*   - the two byte-list spines and the exported theorems.                    *)
(*   - the constant-time and memory-safety proof.                             *)
(* ========================================================================== *)


(* The specification vocabulary and lemmas shared with the other AES-GCM
   proofs (ctr_block, nist_input_block, htable_mem_8, HTABLE_MEM_8_FLAT,
   gcm_wb_blocks, IVAL_WORD_SMALL, DISCARD_STALE_TAC, ...). *)
needs "arm/proofs/utils/aes_gcm_common.ml";;

(* ========================================================================= *)
(* Known-answer instances of htable_mem_8 at two concrete AES-128 keys.      *)
(*                                                                           *)
(* In the shared AES-GCM vocabulary the GHASH key is                         *)
(* H = aes128_cipher (word 0) rk, with rk the FIPS-197 key schedule, and the *)
(* key table precondition of the 8-way kernels is                            *)
(* htable_mem_8 (ghash_twist H) htbl_p s.  Below that precondition is        *)
(* evaluated, for the all-zero key and for the FIPS-197 Appendix B key (the  *)
(* key schedules of common/fips197.ml), to the 12 table entries.  They are   *)
(* the bytes gcm_init_v8 writes for those keys, and the bytes                *)
(* ref_gcm_init_htable writes in the C test "aes_gcm_htable" (tests/test.c), *)
(* so they tie the precondition to the real table: stated with a wrong H,    *)
(* such as the byte-reversed one at the end, it does not match them.         *)
(* ========================================================================= *)


(* All-zero key: H = 66e94bd4ef8a2c3b884cfa59ca342b2e. *)

let HTABLE_MEM_8_AESAVS_ZERO_KEY_128 = prove
 (`!ptr s.
     htable_mem_8
       (ghash_twist (aes128_cipher (word 0) AESAVS_ZERO_KEY_128_SCHEDULE))
       ptr s <=>
     read (memory :> bytes128 ptr) s =
       word 0x1099f4b39468565ccdd297a9df145877 /\
     read (memory :> bytes128 (word_add ptr (word 16))) s =
       word 0x62d81a7fe5da3296dd4b631a4b7c0e2b /\
     read (memory :> bytes128 (word_add ptr (word 32))) s =
       word 0xea0b3a488cb9209b88d320376963120d /\
     read (memory :> bytes128 (word_add ptr (word 48))) s =
       word 0x35c1a04f8bfb23958695e702c322faf9 /\
     read (memory :> bytes128 (word_add ptr (word 64))) s =
       word 0xb2261b4d0cb1e020b354474d48d9d96c /\
     read (memory :> bytes128 (word_add ptr (word 80))) s =
       word 0xe4adc23e440c7165568bd97348bd9145 /\
     read (memory :> bytes128 (word_add ptr (word 96))) s =
       word 0x7d845b630bb0a55df9151b1f632d10b4 /\
     read (memory :> bytes128 (word_add ptr (word 112))) s =
       word 0xa674eba8f9d7f2508491407c689db5e9 /\
     read (memory :> bytes128 (word_add ptr (word 128))) s =
       word 0x4af32418184aee1eec87cfb0e19d1c4e /\
     read (memory :> bytes128 (word_add ptr (word 144))) s =
       word 0xf109e6e0b31d1eee7d1998bcfc545474 /\
     read (memory :> bytes128 (word_add ptr (word 160))) s =
       word 0x7498729da40cd2808c107e5c4f494a9a /\
     read (memory :> bytes128 (word_add ptr (word 176))) s =
       word 0xa47c653dfbeac924d0e417a05fe61ba4`,
  REPEAT GEN_TAC THEN
  CONV_TAC(LAND_CONV(HTABLE_MEM_8_KEY_CONV aes128_cipher
                       AESAVS_ZERO_KEY_128_SCHEDULE)) THEN
  REFL_TAC);;

(* FIPS-197 Appendix B key 2b7e151628aed2a6abf7158809cf4f3c:                *)
(* H = 7df76b0c1ab899b33e42f047b91b546f.                                    *)

let HTABLE_MEM_8_AES128_APPENDIX_B_KEY = prove
 (`!ptr s.
     htable_mem_8
       (ghash_twist (aes128_cipher (word 0) AES128_APPENDIX_B_KEY_SCHEDULE))
       ptr s <=>
     read (memory :> bytes128 ptr) s =
       word 0x7c85e08f7236a8defbeed61835713366 /\
     read (memory :> bytes128 (word_add ptr (word 16))) s =
       word 0xed6f9f19824188b7876b369747479bb8 /\
     read (memory :> bytes128 (word_add ptr (word 32))) s =
       word 0x75fc1bd05afdf91d989384c9d8bc71aa /\
     read (memory :> bytes128 (word_add ptr (word 48))) s =
       word 0x079dada037f75a219393f2f6b5901aa5 /\
     read (memory :> bytes128 (word_add ptr (word 64))) s =
       word 0x5c266e54fcbe70c8940e5f5682674084 /\
     read (memory :> bytes128 (word_add ptr (word 80))) s =
       word 0x4cd5a7571d1a07eb10f3c903e1a47723 /\
     read (memory :> bytes128 (word_add ptr (word 96))) s =
       word 0x1868d687e354011277b65543fd05070d /\
     read (memory :> bytes128 (word_add ptr (word 112))) s =
       word 0x90da1b5ab6308b846fde83c41e51061f /\
     read (memory :> bytes128 (word_add ptr (word 128))) s =
       word 0x43c1c170f6d1cb18d31bda2a40e1409c /\
     read (memory :> bytes128 (word_add ptr (word 144))) s =
       word 0x71a7fa7ec9a2db6a9942b75d8497af5b /\
     read (memory :> bytes128 (word_add ptr (word 160))) s =
       word 0xdff6bfdf58dc7226e8e54d234d357431 /\
     read (memory :> bytes128 (word_add ptr (word 176))) s =
       word 0xbfae27a59d0f85db6058987ac5d3f7fd`,
  REPEAT GEN_TAC THEN
  CONV_TAC(LAND_CONV(HTABLE_MEM_8_KEY_CONV aes128_cipher
                       AES128_APPENDIX_B_KEY_SCHEDULE)) THEN
  REFL_TAC);;

(* The byte-reversed key word_reversefields 8 H (the little-endian reading   *)
(* of AES_K(0^128)) describes a different table: at the all-zero key none of *)
(* its 12 entries equals the real one, so a key-table precondition stated    *)
(* with it is not satisfied by the table gcm_init_v8 builds.                 *)

let HTABLE_MEM_8_AESAVS_ZERO_KEY_128_REVERSED_H = prove
 (`!ptr s.
     htable_mem_8
       (ghash_twist (aes128_cipher (word 0) AESAVS_ZERO_KEY_128_SCHEDULE))
       ptr s
     ==> ~htable_mem_8
            (ghash_twist (word_reversefields 8
               (aes128_cipher (word 0) AESAVS_ZERO_KEY_128_SCHEDULE)))
            ptr s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HTABLE_MEM_8_AESAVS_ZERO_KEY_128] THEN
  CONV_TAC(RAND_CONV(RAND_CONV(HTABLE_MEM_8_KEY_CONV aes128_cipher
                                 AESAVS_ZERO_KEY_128_SCHEDULE))) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV);;

(* ========================================================================= *)
(* Binary-independent proof machinery.                                        *)
(*                                                                            *)
(* Contents:                                                                  *)
(*   - the GHASH/Karatsuba bridge lemma layer (KARATSUBA_LIMBS_LET,           *)
(*     GHASH_1BLOCK_CORRECT, GMULT_REDUCE_PROP3, GMULT_FULL_CORRECT_BA, ...); *)
(*   - the SIMD-fold stepping layer (GCM_SIMD_SIMPLIFY_TAC, the per-step-     *)
(*     discard steppers, ARM_VSTEPS_FOLD_TAC, ...);                           *)
(*   - the bridge-close helpers (PMUL_CONG_128, ABBREV_INNER_PMULS_TAC,       *)
(*     QQ0SPLIT, JOINMID, ...);                                               *)
(*   - the N-block bridge infra (JOIN_EQ_SPLIT, SUBW_* lane lemmas,           *)
(*     MERGE_2BLK_TAC, GMULT2_FULL_CORRECT_BA).                               *)
(* It is a copy of the corresponding layer of aes256_gcm_dec_alt.ml, less     *)
(* the AES-256 output specification, so the two proofs can be loaded          *)
(* together.  No machine code is defined here, and no axioms.                 *)
(* ========================================================================= *)

needs "arm/proofs/utils/aes.ml";;
needs "arm/proofs/utils/aes_encrypt_spec.ml";;

(* ========================================================================= *)
(* N-block GHASH Karatsuba layer.                                             *)
(*                                                                            *)
(* Contents: HELPER_3 and GHASH_POLYVAL_ACC_3/4/5 (3/4/5-block Horner        *)
(* unrolling), the KARATSUBA_LIMBS lemmas, and the karatsuba_block_p{l,h,m} / *)
(* kara_acc / pack_corrected / kara_quad_* / project_triples layer, whose    *)
(* KARA_ACC_PACK_HELPER equates the packed XOR-accumulated per-block         *)
(* Karatsuba triples with the XOR of the per-block word_pmul products.       *)
(*                                                                            *)
(* It builds on common/polyval_ghash.ml and common/karatsuba_pmul.ml.          *)
(* ========================================================================= *)


(* ---- GHASH spec extras (3/4/5-block Horner unrolling) ---- *)

(* Helper: polyval_dot(a XOR p, h)*h^2 == a*h^3 + p*h^3 (mod Q), where       *)
(* h^3 = polyval_dot h (polyval_dot h h).  Bridges via INNER_CONG_GEN,        *)
(* after first commuting polyval_dot h h^2 = polyval_dot h^2 h (via pmul_sym). *)

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
(* GHASH_POLYVAL_ACC_4: 4-block Horner unrolling specialization.            *)
(* Derived directly from GHASH_POLYVAL_ACC_BATCHED for list [p;q;r;s].      *)
(* Unfolds h_power 0..3 to the polyval_dot chain (h, h^2, h^3, h^4).         *)
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
(* GHASH_POLYVAL_ACC_5: 5-block Horner unrolling specialization.            *)
(* Derived directly from GHASH_POLYVAL_ACC_BATCHED for list [p;q;r;s;t].    *)
(* Unfolds h_power 0..4 to the polyval_dot chain (h, h^2, h^3, h^4, h^5).    *)
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
(* structural lemmas:                                                         *)
(*                                                                           *)
(*   KARATSUBA_BLOCK_PACKS_TO_PMUL_CLEAN:                                    *)
(*      pack_corrected (pl_k, ph_k, pm_k) = pmul input_k h_k (256-bit)        *)
(*      under the precondition that hk's low half = karatsuba_mid h_k.        *)
(*                                                                           *)
(*   PACK_CORRECTED_XOR (additivity / linearity):                             *)
(*      pack_corrected commutes with XOR in all three arguments.              *)
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

(* Linearity of kara_acc: starting at non-zero (pl0, ph0, pm0) is the same as
   starting at (0,0,0) and XOR-ing the result with the start. *)
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

(* Quad-list = (input, h_tw, hk, h_true) per block. Used to express the bridge
   precondition (every triple must come from a real `h` with byteswap128 + mid). *)
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

(* The key inductive helper: kara_acc on the projected triples, packed,
   equals kara_quad_pmul (XOR of pmul input_k h_k). *)
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
   FAST, REUSABLE GMULTn builder for the AES-GCM decrypt band proofs.

   `build_GMULTn_fast n` returns a pair (PACKn_ID, GMULTn_FULL_CORRECT_BA):
     - PACKn_ID                : decN_tL  =  XOR_k (word_pmul a_k b_k)   (256-bit)
     - GMULTn_FULL_CORRECT_BA  : polyval_reduce_prop3 (XOR_k word_pmul a_k b_k)
                                 expressed in the machine's Karatsuba-limb byteform.

   Method: prove `decN_tL = XOR_k dec1[k]` structurally by XOR-AC over opaque
   pmul atoms (`AC WORD_XOR_ACI`, no bit-blast; a direct WORD_RULE proof of the
   256-bit identity does not scale past N=3), then fold each single-block
   `dec1[k]` to `word_pmul a_k b_k` via PMUL_KARATSUBA.  This is the shared
   GHASH-bridge multiply lemma for every 2..8-block band.

   It needs only the N-block GHASH Karatsuba layer above (PMUL_KARATSUBA /
   KARATSUBA_LIMBS); the shared Prop3 reduction lemma GMULT_REDUCE_PROP3 (+ its
   V0LO helper) is proved here.
   ============================================================================ *)


(* XOR is associative-commutative; used as the rewrite set for the structural
   `decN_tL = XOR_k dec1[k]` normalization (opaque pmul atoms, no bit-blast). *)
let WORD_XOR_ACI = WORD_RULE
  `(!x y:N word. word_xor x y = word_xor y x) /\
   (!x y z:N word. word_xor (word_xor x y) z = word_xor x (word_xor y z)) /\
   (!x y z:N word. word_xor x (word_xor y z) = word_xor y (word_xor x z))`;;

(* Helper: the low 64-bit lane of v0 = word_join aa bb XOR wa.  Used to make
   the GMULT and Prop3 `word_pmul _ W` atoms syntactically identical (pmul is
   opaque to BITBLAST, so the two wv-inputs must match before the lane blast). *)
let V0LO = prove(
  `!aa bb:64 word. !wa:int128.
     word_subword (word_xor (word_join aa bb:int128) wa) (0,64):64 word =
     word_xor bb (word_subword wa (0,64):64 word)`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

(* The shared Prop3 reduction: the GMULT/assembly W-reduction byteform over an
   abstract 256-bit accumulator t equals polyval_reduce_prop3 t.  aa/bb/cc/dd
   are t's four 64-bit lanes; w = 0xC200000000000000.  Reusable at any block
   count (the N-block loop reduces the accumulated 256-bit sum exactly once). *)
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
(*                                                                            *)
(* The counter core of the proof: the per-block CTR increment used by        *)
(* the ARM binary (gcm_ctr_inc), its lane-byte form (GCM_CTR_INC_LANES), the  *)
(* NIST SP 800-38D inc32 and the byteswap bridge between them, and a defined  *)
(* counter iterator (gcm_ctr_inc_iter) so block k's counter composes in a     *)
(* recursion / N-block induction.                                            *)
(*                                                                            *)
(* inc32 is the NIST SP 800-38D increment; see its definition below.       *)
(*                                                                            *)
(* Why this counter vocabulary is private, next to the shared ctr_block of   *)
(* aes_gcm_spec.ml: gcm_ctr_inc is the update in exactly the form the ARM    *)
(* simulation produces (rev32, add, rev32 on the top lane of the ivec        *)
(* register), so the simulated postconditions of the 8x decrypt proof are    *)
(* stated in gcm_ctr_inc / gcm_ctr_inc_iter (and in the proof's own          *)
(* gcm_ctr_add and gcm_ctr_raw).  Restating them would mean re-simulating;   *)
(* instead the exported theorems are moved to ctr_block nonce c through      *)
(* GCM_CTR_INC_ITER_INC32 below and the ctr_block bridge in the proof.       *)
(* ========================================================================= *)


(* ========================================================================= *)
(* The AES-GCM counter increment (the ARM binary's rev32+ADD+rev32).          *)
(*                                                                            *)
(* gcm_ctr_inc ivec = ivec with its top 32-bit lane byte-reversed, +1, and    *)
(* byte-reversed back.                                                        *)
(* ========================================================================= *)

let gcm_ctr_inc = new_definition
 `gcm_ctr_inc (ivec:(128)word) : (128)word =
   word_insert ivec (96,32)
     (word_bytereverse
        (word_add (word_bytereverse
                     (word_subword ivec (96,32):(32)word))
                  (word 1:(32)word)))`;;

(* gcm_ctr_inc as the explicit per-byte lane-shuffle the front simulation     *)
(* emits (rev32 of the top lane incremented, low 96 bits unchanged, all built  *)
(* from 8-bit subwords of ctr0).  One BITBLAST (~1s); used to fold the spec     *)
(* var ctr1 to the form the Q9 keystream readback carries.                     *)
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
(* NIST SP 800-38D inc32 and the byteswap bridge to gcm_ctr_inc.              *)
(* ========================================================================= *)

(* inc32 per NIST SP 800-38D Section 6.2.  Self-contained (word primitives
   only, zero dependencies).  It is the same definition as common/gcm.ml's
   inc32, so loading both files is a benign redefinition.  It is kept local
   because common/gcm.ml also loads the rest of the SP 800-38D specification
   and its KATs, which this proof does not require. *)
let inc32 = new_definition
 `inc32 (cb:128 word) : 128 word =
    let top96:96 word = word_subword cb (32,96) in
    let bot32:32 word = word_subword cb (0,32) in
    word_join top96 (word_add bot32 (word 1 : 32 word)) : 128 word`;;
(* end inc32 *)

(* INC32_GCM_CTR_INC -- the NIST inc32 <-> ARM gcm_ctr_inc counter bridge.     *)
(* Spec-adjacent, but gcm_ctr_inc is an ARM-proof artifact, so this is the     *)
(* natural home for it unless a shared spec layer claims it.                   *)
(*                                                                            *)
(* Byte-order relationship: inc32 increments the LOW 32 bits of its argument   *)
(* (NIST big-endian counter), keeping the top 96; gcm_ctr_inc increments the   *)
(* TOP 32-bit lane viewed byte-reversed.  They are conjugate by a full 128-bit *)
(* byteswap: gcm_ctr_inc x = word_bytereverse (inc32 (word_bytereverse x)).    *)
let GCM_CTR_INC_INC32 = prove
 (`!x:128 word. gcm_ctr_inc x = word_bytereverse (inc32 (word_bytereverse x))`,
  GEN_TAC THEN REWRITE_TAC[gcm_ctr_inc; inc32] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN BITBLAST_TAC);;

(* ========================================================================= *)
(* The counter iterator: block k's CTR input is gcm_ctr_inc_iter k ctr0.      *)
(* Defined (not a tactic phrase) so it composes in a recursion / N-block      *)
(* induction.  Equals ITER k gcm_ctr_inc, so existing ITER lemmas apply.      *)
(* ========================================================================= *)

let gcm_ctr_inc_iter = define
 `gcm_ctr_inc_iter 0 (x:128 word) = x /\
  gcm_ctr_inc_iter (SUC k) (x:128 word) = gcm_ctr_inc (gcm_ctr_inc_iter k x)`;;

(* The iterated NIST bridge.  Lets the spec state block k's                    *)
(* counter NIST-faithfully (ITER k inc32 over the byteswapped ivec) while the  *)
(* proof folds the binary's lanes via gcm_ctr_inc_iter.                        *)
let GCM_CTR_INC_ITER_INC32 = prove
 (`!k x:128 word.
     gcm_ctr_inc_iter k x = word_bytereverse (ITER k inc32 (word_bytereverse x))`,
  INDUCT_TAC THENL
   [REWRITE_TAC[gcm_ctr_inc_iter; ITER; WORD_BYTEREVERSE_BYTEREVERSE];
    ASM_REWRITE_TAC[gcm_ctr_inc_iter; ITER; GCM_CTR_INC_INC32;
                    WORD_BYTEREVERSE_BYTEREVERSE]]);;

(* The AES-XTS byte-list substrate: byte_list_at, bytes_to_int128,           *)
(* int128_to_bytes, and the shared readback machinery.                       *)
needs "arm/proofs/utils/aes_xts_common.ml";;

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

(* ========================================================================= *)
(* Byte-extraction sublemmas for the whole-block byte_list_at bridges of     *)
(* the 8x decrypt proof: a bytes128 read seen as its 16 bytes8 reads, and    *)
(* byte i of an int128 (or of a flattened int128 list) as a word_subword.    *)
(* BYTES128_TO_BYTES8_THM itself lives in aes_xts_common.ml.                 *)
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
(* SECTION 1: GENERIC GCM MACHINERY (direction-agnostic).                     *)
(*                                                                            *)
(* Nothing below this banner (until the DECRYPT-SPECIFIC section at the end)  *)
(* is decrypt-specific: it is word/SIMD algebra, the GHASH/Karatsuba bridge   *)
(* layer, exec-parameterized steppers, and N-block byteform merge/close       *)
(* tactics equally valid for the ENCRYPT binaries.                            *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* SIMD REV64 fold-back lemmas (shared with the GCM gmult spec layer).       *)
(* The ARM simulator expands REV64.16B into a                                *)
(* 4-level nested word_join/word_subword byte tree (128->64->32->16->8).     *)
(* These collapse it back to word_reversefields 8 the instant it appears, so *)
(* the giant (~145k char) term never forms and the final closure is fast.    *)
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

(* ins->ext: the GHASH-tail Karatsuba mids use
   `ext vD.16b,vN.16b,vN.16b,#8` in place of `ins vD.d[0],vN.d[1]` (a false-dep
   break; both consumed lane-0-only, values identical).  The stepper models
   `ext vD,vN,vN,#8` on a 128-bit register as
   `word_subword (word_join vN vN:256 word) (64,128):128 word` (a rot-by-64).
   Every one of the 9 sites consumes ONLY lane 0 downstream (via `eor .8b` or
   `pmull .1d`), i.e. the projection `word_subword (<ext form>) (0,64)`, which
   is exactly the plain lane `word_subword vN (64,64)` that AWS-LC's `ins` gives.
   Collapsing this COMPOSED projection (NOT the standalone register -- that would
   false-fire on the byteswap/REV64 machinery, which uses the same
   word_subword(word_join a a)(64,128) shape) restores the syntactic form of
   the `ins` lane, so ABBREV_INNER_PMULS's setify qq-numbering and every
   downstream tail bridge match as with `ins`.  This is the same identity as
   SJ_COLLAPSE (in the band machinery below), stated here so the per-step
   normalizer below can fire it. *)
let EXT8_LANE0_IS_SUBWORD_HI = prove(
  `!(w:(128)word).
    word_subword (word_subword (word_join w w:(256)word) (64,128):(128)word) (0,64):(64)word =
    word_subword w (64,64)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* Structural normalization lemmas for the GHASH bridge close (from the standalone
   gcm_gmult_v8 proof).  word_insert comes from the INS instr, nested word_subword
   from the EXT instr.  byteswap128 = pure 64-bit half-swap. *)
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
(* GHASH bridge lemmas (recovered from the standalone gcm_gmult proof).       *)
(* These prove the Karatsuba + Prop3 reduction the assembly computes equals   *)
(* the spec-level polyval_dot / ghash_polyval_acc, so the symbolic Q19 result *)
(* at the xi_p store can be bridged to the postcondition.  All are BITBLAST / *)
(* WORD_RULE proofs.                                                          *)
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
(* Decrypt GHASH bridge helper lemma.                                         *)
(* ------------------------------------------------------------------------- *)

(* word_subword (word_insert x (0,64) y) (0,64) = word_subword y (0,64):        *)
(* discards the leftover tag tree x in the Karatsuba cross-term of the dec      *)
(* GHASH byte-form (the high half is inserted then re-extracted as the low).    *)
let INSERT_SUBWORD_KILL = prove(
  `!(x:(128)word) (y:(128)word).
     word_subword ((word_insert x (0,64) y):(128)word) (0,64):(64)word
     = word_subword y (0,64)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* Scalable (a)+(b) decomposition of the GHASH multiply+reduce bridge.         *)
(*                                                                             *)
(* The unroll8 decrypt/encrypt loop accumulates N per-block Karatsuba products *)
(* into Q17/Q18/Q19 and applies ONE shared Prop3 reduction per 8-block         *)
(* iteration.  Factoring the bridge as (a)+(b) below makes both pieces reusable *)
(* at every block count (1/2/4/8), composed with the already-proven, list-     *)
(* generic GHASH_POLYVAL_ACC_BATCHED (common/polyval_ghash.ml):                *)
(*   (a) PMUL_KARATSUBA (common/karatsuba_pmul.ml): the per-block 3-pmull       *)
(*       (lo/hi/mid) byteform = word_pmul a b (the 256-bit product).            *)
(*   (b) GMULT_REDUCE_PROP3 (below): the assembly's W-reduction byteform over   *)
(*       an ABSTRACT 256-bit accumulator t = polyval_reduce_prop3 t.            *)
(* ------------------------------------------------------------------------- *)

(* Helper: the low 64-bit lane of v0 = word_join aa bb XOR wa.  Used to make    *)
(* the GMULT and Prop3 `word_pmul _ W` atoms syntactically identical (pmul is   *)
(* opaque to BITBLAST, so the two wv-inputs must match before the lane blast).  *)
(* (b) The shared Prop3 reduction: the GMULT/assembly W-reduction byteform over  *)
(* an abstract 256-bit accumulator t equals polyval_reduce_prop3 t.  aa/bb/cc/dd *)
(* are t's four 64-bit lanes; w = 0xC200000000000000.  Reusable at any block     *)
(* count (the N-block loop reduces the accumulated 256-bit sum exactly once).    *)
(* The full GHASH multiply+reduce bridge: the byte-level Karatsuba/Prop3 the   *)
(* assembly computes (left-hand side, in terms of 64-bit pmul limbs) equals    *)
(* the spec-level polyval_dot.  Derived from (a) PMUL_KARATSUBA + (b)         *)
(* GMULT_REDUCE_PROP3 + KARATSUBA_LIMBS_LET (lanes of word_pmul a b = the limbs), *)
(* instead of a single monolithic BITBLAST.                                     *)
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
  (* Compose (a)+(b): polyval_dot a b = polyval_reduce_prop3 (word_pmul a b)  [def];
     word_pmul a b = the Karatsuba 256-word assembly K  [(a) PMUL_KARATSUBA];
     polyval_reduce_prop3 K = the W-reduction byteform over K's lanes  [GSYM (b) GMULT_REDUCE_PROP3];
     K's lanes = the p_lo/cross/p_hi limbs  [KARATSUBA_LIMBS_LET]; then the two byteforms are
     identical up to pmul argument order  [WORD_PMUL_SYM]. *)
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
(* REV32 (vector) per-32-bit-lane reversefields bridge.                        *)
(*                                                                             *)
(* The ISA model (arm/proofs/instruction.ml) defines arm_REV32_VEC via        *)
(*   usimd4 (word_reversefields esize) n,                                      *)
(* so arm_REV32_VEC_ALT (= EXPAND_SIMD_RULE) leaves, per 32-bit lane,          *)
(*   word_reversefields esize (word_subword n (32k,32)).                       *)
(* WORD_SIMPLE_SUBWORD_CONV is a NO-OP on word_reversefields (it does not      *)
(* reduce through it), so the wrapper stays stuck; a downstream positional     *)
(* RAND_CONV then lands on a non-combination and raises "RAND_CONV: Not a      *)
(* combination" (without the rewrites below, at front step s267, the          *)
(* 0x444 aese before the 0x448 b.ge).  The decoder only ever emits esize in   *)
(* {8,16} (decode.ml: esize = 8 << size, size in {0,1}; 2,3 -> UNDEFINED), so  *)
(* these two per-lane rewrites -- typed at :(32)word so they never touch the   *)
(* REV64 64-bit-lane word_reversefields above -- cover every REV32 the decoder *)
(* can produce and let the subword chain reduce fully to the staged           *)
(* word_join/word_subword byte form the downstream bridges expect.            *)
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

(* Reduce the stuck per-lane word_reversefields FIRST (fires only on concrete  *)
(* esize 8/16, which decode supplies), then run the normal subword collapse.   *)
(* ORELSEC inside a single TOP_DEPTH_CONV so it is a total no-op on terms with  *)
(* no 32-bit-lane reversefields (never raises unchanged).                      *)
let REV32_LANE_SUBWORD_CONV =
  TOP_DEPTH_CONV
    (GEN_REWRITE_CONV I [WORD_REVERSEFIELDS_8_32; WORD_REVERSEFIELDS_16_32]
     ORELSEC WORD_SIMPLE_SUBWORD_CONV);;

(* Per-step SIMD simplifier core: fold REV64 trees, cancel double half-swaps,
   normalize nested subwords.  Run after each GHASH step so terms stay small. *)
let GCM_SIMD_SIMPLIFY_CORE_TAC =
  SIMD_SIMPLIFY_ASSUM_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE [WORD_SWAP_HALVES_INVOLUTION; EXT8_LANE0_IS_SUBWORD_HI]) THEN
  RULE_ASSUM_TAC(fun th ->
    try CONV_RULE(RAND_CONV(REV32_LANE_SUBWORD_CONV)) th
    with _ -> th);;

(* The REV64 fold needs TWO passes to reach a fixpoint: pass 1 normalizes the
   nested word_subword tree, pass 2 lets the REV64 lane rules (REV64_LOWER_LANE/
   UPPER_LANE/128) match.  A single pass leaves the raw byte-tree (~2.5k chars)
   in read Q8; two passes fold it to ~320 chars.  Applying the core twice is
   enough empirically (the result is a fixpoint). *)
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

(* Straight-line VSTEPS + per-step fold (no branch resolution).  Used for the
   GHASH multiply/reduce tail (steps 333-351), which has no branches.  Keeps the
   GHASH accumulators (Q17/Q18/Q19) and the xi_p store read-back alive while
   folding REV64 byte-trees so the terms stay bounded (~1-2k chars). *)
let ARM_VSTEPS_FOLD_TAC exec range =
  MAP_EVERY (fun n -> ARM_VSTEPS_TAC exec [n] THEN GCM_SIMD_SIMPLIFY_TAC) (range);;

(* GHASH-tail stepper, expressed via the library's standard single-step+discard idiom (the same
   one plain ARM_STEPS_TAC uses) with the SIMD REV64 fold interleaved.  Per step n:
     ARM_VERBOSE_STEP_TAC  -- advance to state s<n>
     GCM_SIMD_SIMPLIFY_TAC -- fold the REV64 byte-tree into Q19 BEFORE the discard
     DISCARD_OLDSTATE_TAC  -- drop all earlier-state reads, keeping s<n>'s (incl. Q19)
     CLARIFY_TAC
   Folding before discarding is essential: the fold collapses the ~49k-char byte-tree into the
   bounded GHASH accumulator term in Q19, which then survives the discard.  Discarding per step
   holds the hypothesis pile flat at ~77 (vs ~1357 if old states were kept), so each step is
   cheap; measured region 333-348 ~8.8s (vs ~90s when every state is kept).
   This is the XTS-style "step and simplify as we go" -- bare ARM_STEPS_TAC already does the
   step+discard; we only add the byte-tree fold that GHASH's REV64s require. *)
let ARM_STEPS_FOLD_DISCARD_TAC exec snums =
  MAP_EVERY
    (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN GCM_SIMD_SIMPLIFY_TAC THEN
              DISCARD_OLDSTATE_TAC s THEN CLARIFY_TAC)
    (statenames "s" snums);;

(* Discard stale flag hypotheses but KEEP read PC (ENSURES_FINAL_STATE_TAC needs the
   final PC value to discharge the PC postcondition). *)
let DISCARD_COUNTER_ONLY_TAC =
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    let s = string_of_term(concl th) in
    try String.sub s 0 7 = "read NF" ||
        String.sub s 0 7 = "read ZF" ||
        String.sub s 0 7 = "read CF" ||
        String.sub s 0 7 = "read VF"
    with _ -> false)));;

(* ------------------------------------------------------------------------- *)
(* GHASH s341 bridge close.  The assembly computes, in Q19 at s341, the       *)
(* Karatsuba+Prop3 GHASH over the block word_xor (brev xi)(brev ct) with KEY  *)
(* byteswap128 h (the htable H is stored twisted; the real GHASH key is        *)
(* byteswap128(read htbl_p)).  GMULT_FULL_CORRECT_BA with b := byteswap128 h   *)
(* makes the lane operands match exactly; we then abbreviate the Karatsuba     *)
(* pmul limbs to opaque atoms, canonicalize their argument order with          *)
(* WORD_PMUL_SYM (via a congruence), and bit-blast the residual structural     *)
(* XOR/join/subword skeleton.  All BITBLAST/WORD_BLAST, no cheat.              *)
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

(* Abbreviate every currently-innermost fully-applied word_pmul to a fresh qqN:int128. *)
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

(* For each pair of pmul-atom definitions, try to prove the atoms equal (same product up to
   argument order via WORD_PMUL_SYM, operands equal by WORD_BLAST) and rewrite to merge them. *)
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
(* N-block GHASH bridge infrastructure, used by the 2..8-block bands.       *)
(*                                                                            *)
(* ========================================================================= *)
(* ========================================================================= *)
(* Helper lemmas for the 2-product GHASH bridge (byte-form-agnostic, so they  *)
(* hold for either direction).                                                *)
(* ========================================================================= *)

(* word_join lane split: reduces a 128-bit word_join equality to two 64-bit   *)
(* lane equalities (so the final close is two small flat XOR identities).      *)
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

(* per-lane reversefields: word_reversefields 8 on a full int128 commutes with *)
(* the 64-bit lane projection (with a lane swap).                              *)
let RF8_SUBWORD = prove(
  `(!x:int128. word_subword (word_reversefields 8 x) (0,64):64 word =
               word_reversefields 8 (word_subword x (64,64):64 word)) /\
   (!x:int128. word_subword (word_reversefields 8 x) (64,64):64 word =
               word_reversefields 8 (word_subword x (0,64):64 word))`,
  CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* subword lane extraction through word_zx / word_shl of the 256-bit Karatsuba *)
(* assembly (for a 64-bit source).                                             *)
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

(* Collapse a 64-bit lane of subword(subword(join a a)(64,128)) to a plain lane *)
(* of a (the duplicated mid-half the wv W-reduction operand produces).          *)
let SUBSUB_JOIN_DUP = prove(
  `(!a:128 word. word_subword (word_subword (word_join a a :256 word) (64,128) :128 word) (0,64) :64 word
                 = word_subword a (64,64)) /\
   (!a:128 word. word_subword (word_subword (word_join a a :256 word) (64,128) :128 word) (64,64) :64 word
                 = word_subword a (0,64))`,
  CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* Abbreviate EVERY `word_subword (a:int128) (lo,64)` subterm in the goal to a   *)
(* fresh 64-bit var, so the residual is a flat word_xor identity over 64-bit     *)
(* vars that WORD_BITWISE_TAC closes.                                            *)
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

(* Fast closer for a merge's operand-equality subgoal (flatten 256-bit Karatsuba *)
(* lanes to 64-bit, abbreviate, WORD_BITWISE -- <1s vs ~90s WORD_BLAST).          *)
let FAST_OPERAND_TAC : tactic =
  REWRITE_TAC[SUBW_XOR_256; SUBW_ZX_256; SUBW_SHL64_256; SUBW_SHL128_256;
              SUBW_ZX128_256; SUBW_SHL64_128_256; SUBW_SHL128_128_256] THEN
  REWRITE_TAC[WORD_XOR_0; SUBSUB_JOIN_DUP; WORD_SUBWORD_SUBWORD;
              JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  ABBREV_ALL_SUBWORDS_TAC THEN
  WORD_BITWISE_TAC;;

(* Targeted pmul-atom merge for the 2-block bridge (one structurally-determined  *)
(* pair per call; FAST_OPERAND_TAC closes the operand equalities).               *)
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
(* GMULT2 fast-reduce bridge.  GMULT2_FULL_CORRECT_BA is the 2-block fused    *)
(* multiply+reduce: the assembly's byteform that XOR-accumulates TWO Karatsuba *)
(* triples then runs the shared W-reduction equals                            *)
(*   polyval_reduce_prop3 (word_pmul a0 b0 XOR word_pmul a1 b1).               *)
(* Built from PMUL_KARATSUBA + GMULT_REDUCE_PROP3 (the W-reduction is proved  *)
(* once), so the reduction is never re-blasted.  The per-block operand        *)
(* transpose (rev64/h <-> brev/byteswap128) is reconciled by MERGE_2BLK_TAC.  *)
(* ------------------------------------------------------------------------- *)

(* GMULT2_FULL_CORRECT_BA: the 2-block fused multiply+reduce byteform =          *)
(* polyval_reduce_prop3 (word_pmul a0 b0 XOR word_pmul a1 b1), built by the     *)
(* shared fast GMULTn builder above.                                             *)
let _, GMULT2_FULL_CORRECT_BA = build_GMULTn_fast 2;;

(* ========================================================================= *)
(* SECTION 2: DECRYPT-SPECIFIC LEMMAS AND TACTICS.                            *)
(*                                                                            *)
(* Everything below is keyed to the DECRYPT dataflow (GHASH input = the RAW   *)
(* loaded ciphertext blocks cph_i, the last block included: no block is       *)
(* masked).  The encrypt analogues differ in which term feeds the             *)
(* GHASH multiply (computed ciphertext), so these do NOT transfer.            *)
(* ========================================================================= *)

(* ========================================================================= *)
(* AES-GCM DECRYPT: the whole-block input and GHASH specification.           *)
(*                                                                           *)
(* The 8x decrypt kernel processes whole 16-byte blocks only, so these specs *)
(* read the input byte buffer `x` as its len DIV 16 whole blocks, and the    *)
(* proof uses them only at len = 16 * N, N >= 1.  Each band's readable       *)
(* wrapper states its postcondition as `gcm_dec128_pt_bytes (16 * N) x ctr0  *)
(* keys` (output, in the AES-128 vocabulary below) and `gcm_dec_final_xi     *)
(* (16 * N) x xi h` (tag), with the block decomposition hidden.  The per-N   *)
(* unfold lemmas GCM_DEC_GHASH_BLOCKS_WHOLE_N and                            *)
(* GCM_DEC128_PT_BYTES_WHOLE_N (N = 1..8) rewrite these back to the explicit *)
(* N-block list a band's body produces, so the wrappers stay sim-free.       *)
(*                                                                           *)
(* Decrypt differs from encrypt only in what GHASH reads: output block k is  *)
(* word_xor ciphertext_k keystream_k, while GHASH runs over the raw          *)
(* ciphertext blocks `bytes_to_int128 (SUB_LIST (16*k,16) x)`, not over the  *)
(* plaintext.                                                                *)
(* ========================================================================= *)


(* ----------------------------------------------------------------------------
   The int128 block-list view of a byte buffer: `m` consecutive 16-byte blocks
   starting at block index `i` (byte offset 16*i), each read as a big int128.
   ---------------------------------------------------------------------------- *)
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
   ---------------------------------------------------------------------------- *)
let gcm_dec_ghash_blocks = new_definition
 `gcm_dec_ghash_blocks (len:num) (x:byte list) : int128 list =
    gcm_dec_blocks_from 0 (len DIV 16) x`;;

(* The final GHASH accumulator Xi written to xi_p: byte-reverse in, run
   ghash_polyval_acc over the byte-reversed block list keyed by byteswap128 h,
   byte-reverse out.  (Matches the band BODY's xi_p postcondition exactly.) *)
let gcm_dec_final_xi = new_definition
 `gcm_dec_final_xi (len:num) (x:byte list) (xi:int128) (h:int128) : int128 =
    word_bytereverse
      (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
         (MAP word_bytereverse (gcm_dec_ghash_blocks len x)))`;;

(* ----------------------------------------------------------------------------
   Per-N unfold lemmas at len = 16*N, N = 1..8 (every band the routine has,
   more_than_1 .. more_than_7 and the 8-block band): the whole-buffer specs as
   the explicit N-block list
     [bytes_to_int128 (SUB_LIST (0,16) x); ...;
      bytes_to_int128 (SUB_LIST (16*(N-1),16) x)].
   ---------------------------------------------------------------------------- *)
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

needs "common/ghash_nist_bridge.ml";;

(* ========================================================================= *)
(* The AES-128 vocabulary.                                                   *)
(*                                                                           *)
(* aes256_gcm_dec_alt.ml states its keystream with the house aes256_encrypt  *)
(* (aes_encrypt_spec.ml) and its CTR output with its own aes_ctr and         *)
(* gcm_dec_pt_bytes.  These are the AES-128 counterparts, so this proof can  *)
(* follow that one step for step:                                            *)
(*   - aes9, the kernel's in-flight keystream tower (nine aese/aesmc rounds  *)
(*     and the final aese, before the last round key is XORed in), and its   *)
(*     reconstruct lemma AES128_XOR_ENCRYPT_RECONSTRUCT;                     *)
(*   - aes128_encrypt, AES-128 in lane order (the byte order of a bytes128   *)
(*     read), defined from the FIPS-197 aes128_cipher so that the bridge to  *)
(*     the shared aes_ctr_block aes128_cipher is definitional;               *)
(*   - the CTR and byte-list vocabulary aes128_ctr, aes128_ctr_bytes and     *)
(*     gcm_dec128_pt_bytes, with their LENGTH/EL lemmas and the per-N        *)
(*     unfolds; the cipher-free gcm_dec_blocks_from, gcm_dec_ghash_blocks    *)
(*     and gcm_dec_final_xi are those of the layer above;                    *)
(*   - the 11-slot key reads RK_ETA_11 and KEY_READS_FROM_WORDLIST.          *)
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

(* The whole tower with the last round key XORed in is AES-128.              *)
let AES128_ENCRYPT_TOWER = prove
 (`!x k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10:int128.
     aes128_encrypt x [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10] =
     word_xor (aes9 x k0 k1 k2 k3 k4 k5 k6 k7 k8 k9) k10`,
  REWRITE_TAC[aes128_encrypt; aes9; AES128_CIPHER_RECONSTRUCT]);;

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

(* word_bytereverse = word_reversefields 8 at :128.                          *)
let BREV_RF8_128 = prove
 (`word_bytereverse (x:int128) = word_reversefields 8 x`,
  REWRITE_TAC[REWRITE_RULE[FUN_EQ_THM] WORD_BYTEREVERSE_REVERSEFIELDS]);;

let BREV_RF8_INV_128 = prove
 (`!x:int128. word_bytereverse (word_reversefields 8 x) = x`,
  REWRITE_TAC[GSYM BREV_RF8_128; WORD_BYTEREVERSE_BYTEREVERSE]);;

(* The keystream of block j, as the internal theorems state it, is the       *)
(* shared aes_ctr_block (aes_gcm_spec.ml).                                   *)
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
(* Key condensation: the abstract round-key list and its 11 bytes128 reads.  *)
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
(* Machine code (print_literal_from_elf "arm/aes_gcm/aes128_gcm_dec_alt.o") *)
(* ------------------------------------------------------------------------- *)

let aes128_gcm_dec_alt_mc = define_assert_from_elf "aes128_gcm_dec_alt_mc"
  "arm/aes_gcm/aes128_gcm_dec_alt.o"
[
  0xd503245f;       (* arm_BTI *)
  0xb4007621;       (* arm_CBZ X1 (word 3780) *)
  0xf240183f;       (* arm_TST X1 (rvalue (word 127)) *)
  0x540075e1;       (* arm_BNE (word 3772) *)
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
  0x5400804d;       (* arm_BLE (word 4104) *)
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
  0x5400172c;       (* arm_BGT (word 740) *)
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
  0x540005ec;       (* arm_BGT (word 188) *)
  0xf10140bf;       (* arm_CMP X5 (rvalue (word 80)) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea41c85;       (* arm_MOV_VEC Q5 Q4 128 *)
  0x4ea31c64;       (* arm_MOV_VEC Q4 Q3 128 *)
  0x4ea11c23;       (* arm_MOV_VEC Q3 Q1 128 *)
  0x540006ac;       (* arm_BGT (word 212) *)
  0xf10100bf;       (* arm_CMP X5 (rvalue (word 64)) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea41c85;       (* arm_MOV_VEC Q5 Q4 128 *)
  0x4ea11c24;       (* arm_MOV_VEC Q4 Q1 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x540007ac;       (* arm_BGT (word 244) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea11c25;       (* arm_MOV_VEC Q5 Q1 128 *)
  0xf100c0bf;       (* arm_CMP X5 (rvalue (word 48)) *)
  0x540008ac;       (* arm_BGT (word 276) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0xf10080bf;       (* arm_CMP X5 (rvalue (word 32)) *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x4ea11c26;       (* arm_MOV_VEC Q6 Q1 128 *)
  0x54000a0c;       (* arm_BGT (word 320) *)
  0xf10040bf;       (* arm_CMP X5 (rvalue (word 16)) *)
  0x4ea11c27;       (* arm_MOV_VEC Q7 Q1 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x54000b6c;       (* arm_BGT (word 364) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x14000069;       (* arm_B (word 420) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e184312;       (* arm_EXT Q18 Q24 Q24 64 *)
  0x0ef9e113;       (* arm_PMULL_VEC Q19 Q8 Q25 64 *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x4ef9e111;       (* arm_PMULL2_VEC Q17 Q8 Q25 64 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0xce01752c;       (* arm_EOR3 Q12 Q9 Q1 Q29 *)
  0x0ef2e372;       (* arm_PMULL_VEC Q18 Q27 Q18 64 *)
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

(* `|- LENGTH aes128_gcm_dec_alt_tmc = 5008`. The nonoverlapping
   preconditions spell the code region as `LENGTH aes128_gcm_dec_alt_tmc`,
   but the store-safety check of the stepper does numeric arithmetic on that
   length, so each simulation first reduces it to the numeral with
   RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]). *)
let WB_MC_LEN = fst AES128_GCM_DEC_ALT_EXEC;;

(* ------------------------------------------------------------------------- *)
(* Definitions and helper lemmas shared with the AES-256 proof               *)
(* (arm/proofs/aes256_gcm_dec_alt.ml, which this proof does not load).       *)
(* htable_mem_dec and gcm_ctr_raw are byte-identical copies of the AES-256   *)
(* definitions, so the two proofs can still be loaded together.              *)
(* ------------------------------------------------------------------------- *)

(* The 12-slot aws-lc key table as one predicate over the GHASH input key h  *)
(* (the slot values are the byteswapped polyval_dot powers and the packed    *)
(* Karatsuba mids).  Expand it (REWRITE_TAC[htable_mem_dec] + let_CONV)      *)
(* before stepping, so that the table loads resolve.                         *)
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

(* The tag load ld1/ext/rev64 leaves Q19 as word_join (reversefields lo)     *)
(* (reversefields hi) of xi; this is word_bytereverse xi.                    *)
let Q19_BREVXI = prove
 (`word_join (word_reversefields 8 (word_subword (xi:int128) (0,64):int64))
             (word_reversefields 8 (word_subword xi (64,64):int64)):int128 =
   word_bytereverse xi`,
  CONV_TAC WORD_BLAST);;

(* gcm_ctr_inc^k ctr0 as the lanes the front's counter setup computes, for   *)
(* k = 2 .. 7 (GCM_CTR_INC_LANES, in the layer above, is k = 1).            *)
let GCM_CTR_INC2_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc ctr0)`,
        subst [`word 2:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;
let GCM_CTR_INC3_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))`,
        subst [`word 3:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;
let GCM_CTR_INC4_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)))`,
        subst [`word 4:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;
let GCM_CTR_INC5_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))))`,
        subst [`word 5:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;
let GCM_CTR_INC6_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)))))`,
        subst [`word 6:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;
let GCM_CTR_INC7_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))))))`,
        subst [`word 7:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;

(* The input buffer, read as whole blocks.  First for a 16 * n-byte prefix of *)
(* x, by induction on n: the top block of a 16 * (n + 1)-byte read, and the   *)
(* 16 * n-byte prefix read the IH takes, are READ_BYTES_AND_BYTE128_MERGE.   *)
(* Then for the whole buffer, the form every consumer has.                   *)
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

(* The raw counter accumulator kept in v30: the counter block byte-grouped   *)
(* as rev32 reads it, with w added to its top 32-bit lane; rev32 of it is    *)
(* the AES input block for counter w.  Machine-level vocabulary, like        *)
(* gcm_ctr_inc: no exported statement mentions it.                           *)
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

(* ------------------------------------------------------------------------- *)
(* The shared front: the entry pc+0x1c to the 0x340 b.ge (pc+832), steps     *)
(* 1..201.  It loads ivec, the tag and the 11 round keys, computes the 8     *)
(* counter blocks from the reversed base counter and the increments +1..+7   *)
(* (one add and one rev32 each) and runs the 8 keystream                     *)
(* towers up to the final aese (aes9); it reads no input block and no key    *)
(* table entry, and its one data-dependent branch before the 0x340 b.ge is   *)
(* the dispatch b.le at step 8, which falls through for nblk >= 5, so it is  *)
(* proved once on the union band 5 <= nblk /\ 128 * nblk < 2 EXP 64, with X5 *)
(* general and the raw flags of cmp x0,x5 kept.  The 5..8 leg                *)
(* (WB_FRONT_BUF) takes the b.ge and runs the 5 tail-entry steps to the      *)
(* shared seam pc+3032; the >=9 leg falls through to the front-N.            *)
(* ------------------------------------------------------------------------- *)

let wb_front_pre_tm = `\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
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
          htable_mem_dec h htbl_p s`;;

let wb_front_frame_tm = `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(out_p:int64, 16 * nblk); memory :> bytes(xi_p:int64, 16);
                 memory :> bytes(ivec_p:int64, 16); memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31]`;;

let wb_front_hyps_tm = `5 <= nblk /\ nblk <= 8 /\ LENGTH (ibytes:byte list) = 16 * nblk /\
    aligned 16 stackpointer /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (out_p:int64, 16 * nblk) /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (xi_p:int64, 16) /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (ivec_p:int64, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 16 * nblk) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 176) /\
    nonoverlapping (ivec_p, 16) (htbl_p:int64, 192) /\
    nonoverlapping (in_p, 16 * nblk) (stackpointer, 80) /\
    nonoverlapping (key_p, 176) (stackpointer, 80) /\
    nonoverlapping (htbl_p, 192) (stackpointer, 80) /\
    nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
    nonoverlapping (xi_p, 16) (in_p, 16 * nblk) /\
    nonoverlapping (xi_p, 16) (key_p, 176) /\
    nonoverlapping (xi_p, 16) (htbl_p, 192) /\
    nonoverlapping (xi_p, 16) (stackpointer, 80)`;;

let wb_front_vars = [`pc:num`;`stackpointer:int64`;`out_p:int64`;`xi_p:int64`;`ivec_p:int64`;
            `in_p:int64`;`key_p:int64`;`htbl_p:int64`;`nblk:num`;`ibytes:byte list`;
            `xi:int128`;`ctr0:int128`;`k0:int128`;`k1:int128`;`k2:int128`;`k3:int128`;
            `k4:int128`;`k5:int128`;`k6:int128`;`k7:int128`;`k8:int128`;`k9:int128`;
            `k10:int128`;`h:int128`];;

let mk_wb_front_goal postcond =
  let ens = subst [wb_front_pre_tm,`PPP:armstate->bool`; postcond,`QQQ:armstate->bool`;
                   wb_front_frame_tm,`CCC:armstate->armstate->bool`]
              `ensures arm PPP QQQ CCC` in
  list_mk_forall(wb_front_vars, mk_imp(wb_front_hyps_tm, ens));;

(* The postconditions state the 8 in-flight keystream towers folded to       *)
(* aes9 (gcm_ctr_inc^i ctr0) k0 .. k9; wb_front_fold_tac applies the same    *)
(* fold to the simulated assumptions before final-state matching.            *)
let wb_ctr_lanes_thms =
  [GCM_CTR_INC_LANES; GCM_CTR_INC2_LANES; GCM_CTR_INC3_LANES; GCM_CTR_INC4_LANES;
   GCM_CTR_INC5_LANES; GCM_CTR_INC6_LANES; GCM_CTR_INC7_LANES];;
let wb_front_fold_tac =
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM aes9]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE(map GSYM wb_ctr_lanes_thms));;

(* ---- term builders for the simulated postconditions ----------------------
   Each postcondition below describes the final state of a simulation: the
   aligned_bytes_loaded fact and the `read _ sN = _` assumptions (after
   wb_front_fold_tac), with sN abstracted to s.  They are built from the term
   families below. *)

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
(* the keystream tower aes9 ctr k0 .. k9 *)
let wbp_aes9 ctr =
  list_mk_comb(`aes9`, ctr :: map (fun i -> mk_var("k"^string_of_int i,`:int128`)) (0--9));;
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
(* the key schedule k0 .. k10 and the 12 htable_mem_dec slots, as read from memory *)
let wbp_key_reads =
  map (fun i -> mk_eq(wbp_mem128 `key_p:int64` i, mk_var("k"^string_of_int i,`:int128`))) (0--10);;
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
   offsets a, b, c, d; wbp_lane b is the 32-bit lane of ctr0 at bit b grouped as
   gcm_ctr_raw groups it, wbp_revlane b the same bytes in the opposite order *)
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
(* v30 after the front's add v30 steps: top lane + w, then + 1; the other lanes + 0 *)
let wbp_raw_acc w =
  wbp_join128 (wbp_add32 (wbp_add32 (wbp_lane 96) w) 1) (wbp_add32 (wbp_lane 64) 0)
              (wbp_add32 (wbp_lane 32) 0) (wbp_add32 (wbp_lane 0) 0);;
(* rev32 of the raw counter with top lane + w: the AES input block for counter w *)
let wbp_rev_ctr w =
  wbp_join128 (wbp_bytes4 (wbp_add32 (wbp_lane 96) w) [0; 8; 16; 24])
              (wbp_revlane 64) (wbp_revlane 32) (wbp_revlane 0);;
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
(* decrypted block i, word_xor (word_xor cph_i (aes9 ctr_i k0..k9)) k10, and its store *)
let wbp_pt i = mk_comb(mk_comb(`word_xor:int128->int128->int128`,
  mk_comb(mk_comb(`word_xor:int128->int128->int128`, mk_cph i), wbp_aes9 (mk_ctr i))), `k10:int128`);;
let wbp_out i = mk_eq(wbp_mem128 `out_p:int64` i, wbp_pt i);;

(* the in-flight keystream tower of block i in register Qi *)
let wbp_towers = map (fun i -> wbp_rd (mk_const("Q"^string_of_int i,[])) (wbp_aes9 (mk_ctr i))) (0--7);;

(* The seam state at pc+3032, after the 0x340 b.ge is taken (nblk <= 8) and
   the tail entry has run mov v29,v27 (Q29 = k10), sub x5,x4,x0
   (X5 = 16 * nblk), cmp x5,#0x70, ldp q24,q25,[x6,#160] (the key table
   slots 160 and 176) and ldr q9,[x0],#16 (input block 0).  The front sets
   v30 to the base counter + 7 and adds the increment once more, so
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
   `read X3 s = xi_p`;
   `read X6 s = htbl_p`;
   `read (memory :> bytes (in_p,16 * nblk)) s = num_of_bytelist ibytes`;
   `read (memory :> bytes128 xi_p) s = xi`;
   `read (memory :> bytes128 ivec_p) s = ctr0`] @
  wbp_key_reads @ wbp_htable_reads @
  [mk_eq(wbp_mem128 `in_p:int64` 0, mk_cph 0)] @ wbp_ctx `xi:int128` @
  [`read X5 s = word (16 * nblk)`;
   `read X0 s = word_add in_p (word 16)`;
   wbp_rd `Q9` (mk_cph 0);
   `read Q29 s = k10`;
   `read Q30 s = gcm_ctr_raw (word 8) ctr0`]);;

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

(* the two nblk-dependent scalar values: x9 = len_bits >> 3 and              *)
(* x5 = (x9 - 1) AND -128, the byte length of the main-loop part             *)
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
  REWRITE_TAC[WORD_ARITH
   `word 18446744073709551488:int64 = word_not(word(2 EXP 7 - 1))`;
   WORD_AND_NOT_MASK_WORD] THEN
  SIMP_TAC[VAL_WORD_SUB_CASES; VAL_WORD_1; VAL_WORD_EQ; DIMINDEX_64;
           ARITH_RULE `2 EXP 7 = 128`; ARITH_RULE `1 <= n ==> 1 <= 16 * n`;
           ARITH_RULE `(16 * n - 1) DIV 128 = (n - 1) DIV 8`]);;

(* 128 * ((nblk - 1) DIV 8) = 0 for 1 <= nblk <= 8 (the 5..8 band takes the  *)
(* 0x340 b.ge)                                                               *)
let D_ZERO_LE8 = prove
 (`!nblk. 1 <= nblk /\ nblk <= 8 ==> 128 * ((nblk - 1) DIV 8) = 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(nblk - 1) DIV 8 = 0` (fun th -> REWRITE_TAC[th; MULT_CLAUSES]) THEN
  MATCH_MP_TAC DIV_LT THEN ASM_ARITH_TAC);;

(* The dispatch cmp x9,#0x40 ; b.le w5r_small at 0x34/0x38 (steps 7, 8),     *)
(* with x9 = word (16 * nblk) from the lsr x9,x1,#3: for nblk >= 5 the b.le  *)
(* falls through (16 * nblk >= 80 > 64), and the front runs on; nblk <= 4    *)
(* takes the 1-4 block path (WB_FUSED_kBLOCK below).  GUARD_LE_FALLTHRU      *)
(* resolves the branch condition for 5 <= nblk; the prebranch stepper adds  *)
(* it to the assumptions before stepping 7-8 so that the stepper folds the  *)
(* branch to the fall-through.                                               *)
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

(* The union band: the 5..8 hypotheses without nblk <= 8, plus               *)
(* 128 * nblk < 2 EXP 64.  Its consumers (bands 5..8 and the >=9 chain) all  *)
(* lie on the fall-through side of the dispatch.                             *)
let wbn_front_hyps_uni_tm =
  let cs8 = conjuncts wb_front_hyps_tm in
  end_itlist (curry mk_conj)
    (`5 <= nblk`::`128 * nblk < 2 EXP 64`::
     (filter (fun c -> not(c = `5 <= nblk` || c = `1 <= nblk` || c = `nblk <= 8`)) cs8));;

let NBLK_ARITH_UNI_TAC =
  MP_TAC(ASSUME `5 <= nblk`) THEN MP_TAC(ASSUME `128 * nblk < 2 EXP 64`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;;

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

(* Steps 1..201.  The dispatch b.le (s8) falls through (GUARD_LE_FALLTHRU); *)
(* the increments +2..+7 (s16-s21) reduce to word constants; the tag load   *)
(* (s22-s24) is folded by Q19_BREVXI; each step of the counter setup        *)
(* (s25-s56: the base rev32, the adds and rev32s of blocks 1..7) and the    *)
(* eighth add at s174 is followed by GCM_SIMD_SIMPLIFY_TAC, which leaves    *)
(* flat word_add lanes that GSYM wb_ctr_lanes_thms folds to                 *)
(* gcm_ctr_inc^k ctr0.                                                       *)
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
   `read X3 s = xi_p`;
   `read X6 s = htbl_p`;
   `read (memory :> bytes (in_p,16 * nblk)) s = num_of_bytelist ibytes`;
   `read (memory :> bytes128 xi_p) s = xi`;
   `read (memory :> bytes128 ivec_p) s = ctr0`] @
  wbp_key_reads @ wbp_htable_reads @
  [mk_eq(wbp_mem128 `in_p:int64` 0, mk_cph 0)] @ wbp_ctx `xi:int128`);;

(* THE SHARED PRE-BRANCH PREFIX LEMMA *)
let WBN_FRONT_PREBRANCH = prove(mk_wbn_prebranch_goal wbn_front_prebranch_postcond,
  WBN_FRONT_PREBRANCH_TAC THEN wb_front_fold_tac THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_ADD_0] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC);;

(* THE 5..8 FRONT: WBN_FRONT_PREBRANCH, then the 0x340 b.ge taken (X5 = in_p *)
(* for nblk <= 8, so cmp x0,x5 compares equal) and the 5 tail-entry steps    *)
(* 0xbc4..0xbd4 to the seam pc+3032, in WBN_FRONT_TO_PREP_916's shape: one   *)
(* simplification first (X5 = in_p by D_ZERO_LE8, so NF = VF = F and the     *)
(* stepper takes the b.ge; the ABI frame unfolded for the final state), and  *)
(* a close for the sub x5,x4,x0 value and v30's top lane, the front's        *)
(* base + 7 then + 1, as gcm_ctr_raw (word 8) ctr0.                          *)
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

(* ------------------------------------------------------------------------- *)
(* The tail: shared machinery for the back-legs from the seam pc+3032.       *)
(* ------------------------------------------------------------------------- *)

(* The GHASH-tail stepper (the AES-256 one).  The tail's Karatsuba mids use *)
(* `ext vD.16b,vN.16b,vN.16b,#8`, of which only lane 0 is read (by an .8b    *)
(* eor or a .1d pmull); the normalizer's EXT8_LANE0_IS_SUBWORD_HI folds that *)
(* projection to the plain lane `word_subword vN (64,64)`.  The odd-block    *)
(* chains use `mov v27.d[1],v27.d[0]` + pmull2 with the hk slot, which the   *)
(* stepper leaves as word_insert / word_subword operands of the pmuls; the   *)
(* GHASH bridges prove these equal to the spec's operands when they merge    *)
(* the pmul atoms.                                                           *)
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
let gcm_simd_kgh_tbl : (term,unit) Hashtbl.t = Hashtbl.create 4096;;
let CLEAR_KEEPGH_MEMO_TAC : tactic =
  fun (asl,w) -> Hashtbl.clear gcm_simd_kgh_tbl; ALL_TAC (asl,w);;
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

(* Plaintext capture: read q sn = word_xor (word_xor cph (aes9 ctr ..)) k10   *)
(* (the eor3 with the ciphertext and k10) is word_xor cph (aes128_encrypt ..). *)
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

(* The 1-block GHASH bridge: the spec side is unfolded by GMULT_FULL_CORRECT_BA *)
(* and both sides are reduced to the same three pmul atoms (T's bridge up to  *)
(* the lane normalization); what is left is GF(2)-linear in three 128-bit     *)
(* atoms, which BITBLAST_TAC decides directly.  The eor3s of the tail's final *)
(* reduction (0xe88, 0xe94) only reorder that linear form.                    *)
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

(* The 2-block GHASH bridge: T's WB2_GMULT2_BRIDGE_TAC up to its lane       *)
(* normalization (GHASH_POLYVAL_ACC_2 unfolded by GMULT2_FULL_CORRECT_BA,    *)
(* the pmul atoms merged by MERGE_2BLK_TAC), then BITBLAST_TAC on the        *)
(* remaining GF(2)-linear identity, whose shape the tail's eor3 reduction    *)
(* changes.                                                                  *)
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

(* ---- buffer-form band statements ------------------------------------------ *)
let mk_outp_read i =
  let addr = if i = 0 then `out_p:int64`
    else subst [mk_small_numeral(16*i),`nnn:num`] `word_add out_p (word nnn):int64` in
  subst [addr,`aaa:int64`] `read (memory :> bytes128 (aaa:int64)) s:int128`;;
let mk_out_conj i =
  mk_eq(mk_outp_read i,
    subst [mk_cph i,`ccc:int128`; mk_ctr i,`ttt:int128`]
      `word_xor (ccc:int128) (aes128_encrypt (ttt:int128)
        [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10])`);;
let mk_ghash_list k =
  mk_flist(map (fun i -> mk_comb(`word_bytereverse:int128->int128`, mk_cph i)) (0--(k-1)));;

(* The band-exit counter write-back conjunct, spine form
   read [ivec_p] = gcm_ctr_inc_iter k ctr0 (used by mk_band_goal + WB_TAIL close). *)
let mk_ivec_conj k = subst [mk_small_numeral k,`kkk:num`]
    `read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter kkk ctr0`;;

let mk_band_goal k =
  let n16 = mk_small_numeral(16*k) and n128 = mk_small_numeral(128*k) in
  let hyps = subst [n16,`sss:num`]
    `LENGTH (ibytes:byte list) = sss /\
     aligned 16 stackpointer /\
     nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (stackpointer:int64, 80) /\
     nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (out_p:int64, sss) /\
     nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (xi_p:int64, 16) /\
     nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (ivec_p:int64, 16) /\
     nonoverlapping (out_p, sss) (xi_p, 16) /\
     nonoverlapping (out_p, sss) (ivec_p, 16) /\
     nonoverlapping (xi_p, 16) (ivec_p, 16) /\
     nonoverlapping (ivec_p, 16) (in_p:int64, sss) /\
     nonoverlapping (ivec_p, 16) (key_p:int64, 176) /\
     nonoverlapping (ivec_p, 16) (htbl_p:int64, 192) /\
     nonoverlapping (in_p, sss) (stackpointer, 80) /\
     nonoverlapping (key_p, 176) (stackpointer, 80) /\
     nonoverlapping (htbl_p, 192) (stackpointer, 80) /\
     nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
     nonoverlapping (xi_p, 16) (in_p, sss) /\
     nonoverlapping (xi_p, 16) (key_p, 176) /\
     nonoverlapping (xi_p, 16) (htbl_p, 192) /\
     nonoverlapping (xi_p, 16) (stackpointer, 80) /\
     nonoverlapping (out_p, sss) (in_p, sss) /\
     nonoverlapping (out_p, sss) (key_p, 176) /\
     nonoverlapping (out_p, sss) (htbl_p, 192) /\
     nonoverlapping (out_p, sss) (stackpointer, 80)` in
  let pre = subst [n16,`sss:num`; n128,`bbb:num`]
    `\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
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
        htable_mem_dec h htbl_p s` in
  let pc_post = `read PC s = word (pc + 3756)` in
  let x9_post = subst [n16,`sss:num`] `read X9 s = word sss` in
  let outs = map mk_out_conj (0--(k-1)) in
  let xi_post = subst [mk_ghash_list k,`lll:int128 list`]
    `read (memory :> bytes128 xi_p) s =
     word_bytereverse
       (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi) (lll:int128 list))` in
  (* The counter write-back at band exit r, spine form gcm_ctr_inc_iter r
     ctr0 (= gcm_ctr_add (word r) ctr0); closed by WB_IVEC_CLOSE_TAC r. *)
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

(* ---- recomposition machinery ---------------------------------------------- *)
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
          `k8:int128`;`k9:int128`;`k10:int128`;`h:int128`] WB_FRONT_BUF);;
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

(* Back-leg prep for band k: init at the seam, derive input lanes 1..k-1,
   abbreviate the cph names and the h powers so that the per-band tail
   tactics apply.  The seam state is named s199, and the tail steps are
   numbered on from it: s200, s201, ... *)
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
  CLEAR_KEEPGH_MEMO_TAC THEN  (* reset the KEEPGH normalizer fixpoint cache per tail body *)
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN ENSURES_INIT_TAC "s199" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV WORD_REDUCE_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  lanes THEN cphs THEN habbrevs;;

(* ========================================================================= *)
(* The shared per-block back-leg, proved once per residue.                    *)
(*                                                                            *)
(* The back-leg sim `WB_PREP_TAC k THEN WB_TAIL_k_TAC` (seam pc+3032 to the   *)
(* core exit pc+3756) is proved once per k as WB_TAIL_GEN2_k, from a strictly *)
(* weaker precondition than prove_band's (q_at k minus 5 cells the tail does  *)
(* not read).  Both goals share the post and frame of mk_band_goal k, so the  *)
(* weak-precondition back-leg implies the full one by conjunct-drop           *)
(* weakening (ENSURES_PRECONDITION_THM, no re-simulation), and WB_TAIL_GEN2_k *)
(* serves both prove_band (below) and the nblk > 8 recomposition.            *)
(*                                                                            *)
(* The 5 dropped cells (sp+72, xi_p, ivec_p, in_p block 0, X1) are never     *)
(* read by the tail range [0xbd8,0xeac) or the exact-8 drain [0xecc,0x1040). *)
(* X9 is also unread, but is kept generically as `return_value` so the proof *)
(* records that the byte count survives to the `mov x0,x9` at the core exit. *)
(* Each WB_TAIL_GEN2_k proving hyps = 0 is the in-proof audit of both facts. *)
(* ------------------------------------------------------------------------- *)

(* the band goal split into (vars, hyps, pre, post, frame) *)
let wbn_dissect_band k =
  let g = mk_band_goal k in
  let vars, body = strip_forall g in
  let hyps, ens = dest_imp body in
  let _, args = strip_comb ens in
  (vars, hyps, el 1 args, el 2 args, el 3 args);;

(* the 4 seam cells the weak seam drops: [sp+72] = 0 is a pinned artifact;   *)
(* xi_p and ivec_p are consumed only via Q19 and Q0..Q7, Q30; in_p block 0   *)
(* arrives pre-loaded in Q9.                                                 *)
let wbn_tail_drop_lhs = [
  `read (memory :> bytes64 (word_add stackpointer (word 72))) (s:armstate)`;
  `read (memory :> bytes128 xi_p) (s:armstate)`;
  `read (memory :> bytes128 ivec_p) (s:armstate)`;
  `read (memory :> bytes128 in_p) (s:armstate)`];;

(* Replace the fixed per-band X9 count with a generic value.  The residual    *)
(* tail is shared by fixed bands (return_value = 16*r) and shifted whole-call *)
(* tails (return_value = 16*nblk), and it does not write X9.                  *)
let wbn_replace_x9 value pred =
  let sv, body = dest_abs pred in
  let x9lhs = subst [sv,`s:armstate`] `read X9 s` in
  let cs = conjuncts body in
  let cs' = map (fun c ->
    if is_eq c && lhs c = x9lhs then mk_eq(x9lhs,value) else c) cs in
  mk_abs(sv, end_itlist (curry mk_conj) cs');;

(* 5-cell drop: the 4 memory cells plus dead X1; X9 stays in the contract.    *)
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

(* ------------------------------------------------------------------------- *)
(* 2. Symbolic counter layer: gcm_ctr_add w = "add w to the be-top-lane".    *)
(*    Gives the invariant a closed counter form at symbolic block index:     *)
(*    gcm_ctr_inc_iter k x = gcm_ctr_add (word k) x.                         *)
(*                                                                           *)
(*    OOM WARNING: do NOT prove GCM_CTR_ADD_LANES by direct BITBLAST -- the  *)
(*    symbolic 32-bit addend makes the BDD blow past 30GB.  The factoring    *)
(*    below keeps every BITBLAST wiring-only                                  *)
(*    (word_add never meets the BDD); whole layer proves in <1s.             *)
(* ------------------------------------------------------------------------- *)

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

(* wiring-only: insert of brev s as the byte-join tower; s stays FREE so the
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

(* the 4 lane-extraction lemmas (used to prove GCM_CTR_RAW_INCR without a
   symbolic-w WORD_BLAST, which OOMs -- see the Sec 2 OOM WARNING).  Each proves fast
   via WORD_SIMPLE_SUBWORD_CONV (extracts the lane) then WORD_BLAST (w appears
   only additively in the top lane, the addend never enters the BDD). *)
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

(* the increment: `add v30.4s,v30.4s,v31.4s` (v31 = word 2^96) is a lane-wise
   32-bit add; the model emits it as word_join of word_add(word_subword v30 lane)(word c)
   with c=1 on the top lane, 0 elsewhere.  This advances the raw counter by 1. *)
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
(* The band-tail ivec write-back closer.                                      *)
(*                                                                            *)
(* Each band r stores rev32(v30) to [ivec_p] (rev32 v30 / str q30,[x16] at    *)
(* 0xea4/0xea8, the last two tail instructions, after the tag store).  With   *)
(* Q30 = gcm_ctr_raw (word 8) ctr0 carried in from the seam, the store value  *)
(* is Q30 after (8-r) `sub v30` decrements: gcm_ctr_raw (word 8) minus (8-r)  *)
(* = gcm_ctr_raw (word r), and rev32 of that = gcm_ctr_add (word r) =         *)
(* gcm_ctr_inc_iter r ctr0.  The close runs entirely in 32-bit-lane algebra   *)
(* (SUBW_RAW_* pins the sub cascade to the top lane; GCM_CTR_ADD_LANES gives  *)
(* the rev target), so no 128-bit blast meets the symbolic counter.          *)
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

(* ------------------------------------------------------------------------- *)
(* Per-band tail tactics, from the seam s199 (pc+3032) to the core exit      *)
(* pc+3756.  Each block's plaintext is captured as soon as its eor3 with the *)
(* ciphertext and k10 lands in Q12, the residue cascade is stepped with the  *)
(* Q30 normalizer, the GHASH multiply/reduce with the KEEPGH stepper, and    *)
(* the tag is bridged at the last eor3 of the shared reduction (0xe94).      *)
(* ------------------------------------------------------------------------- *)

(* r = 1: s203 eor3 (block-0 plaintext), s204-s250 the cascade to 0xe44,    *)
(* s251-s258 the block-0 GHASH multiply, s259 st1 (output store), s260-s271  *)
(* the reduction, s272/s273 ext/rev64, s274 tag store, s275/s276 rev32 v30 / *)
(* str q30,[x16] (ivec write-back).                                          *)
let WB_TAIL_1_TAC ivtac =
  ARM_STEPS_RESOLVE_TAC AES128_GCM_DEC_ALT_EXEC (200--203) THEN
  WB_PT_CAPTURE_TAC "s203" `Q12` `cph:int128` `ctr0:int128` THEN
  ARM_STEPS_RESOLVE_Q30_TAC AES128_GCM_DEC_ALT_EXEC (204--251) THEN
  ARM_STEPS_FOLD_KEEPGH_TAC AES128_GCM_DEC_ALT_EXEC (252--258) THEN
  (* 259 = st1 {v12.16b},[x2] (output store); carry the readback across the discard *)
  ARM_VSTEPS_FOLD_TAC AES128_GCM_DEC_ALT_EXEC [259] THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 out_p) s259` with _ -> false)
    then MP_TAC th else NO_TAC) THEN
  DISCARD_OLDSTATE_TAC "s259" THEN DISCH_TAC THEN
  ARM_STEPS_FOLD_KEEPGH_TAC AES128_GCM_DEC_ALT_EXEC (260--271) THEN
  (* GHASH bridge at s271 (pc+3736, after eor3 v19,v19,v18,v17) *)
  WB_REPLACE_READ_TAC `read Q19 (s271:armstate)` WB1_GMULT_BRIDGE_TAC
    `polyval_dot (word_xor (word_bytereverse xi) (word_bytereverse cph)) (byteswap128 h)` THEN
  ABBREV_TAC `gval:int128 = polyval_dot (word_xor (word_bytereverse xi)
    (word_bytereverse cph)) (byteswap128 h)` THEN
  (* 272 ext (half-swap), 273 rev64 -> Q19 = word_bytereverse gval *)
  ARM_VSTEPS_FOLD_TAC AES128_GCM_DEC_ALT_EXEC (272--273) THEN
  WB_REPLACE_READ_TAC `read Q19 (s273:armstate)` (CONV_TAC WORD_BLAST)
    `word_bytereverse (gval:int128)` THEN
  (* 274 = st1 {v19.16b},[x3] (tag store); 275/276 = rev32 v30, str q30,[x16] *)
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

(* r = 2: s203 eor3 (block-0 plaintext), s204-s247 the cascade to the taken *)
(* b.gt at 0xc94, s248 st1 (block-0 store, x2 += 16), s249-s259 the block-0 *)
(* GHASH round with h2, s260 eor3 (block-1 plaintext), s261-s272 the block-1 *)
(* round with h, s273 st1 (block-1 store), s274-s285 the reduction,          *)
(* s286/s287 ext/rev64, s288 tag store, s289/s290 the ivec write-back.       *)
let WB_TAIL_2_TAC ivtac =
  ARM_STEPS_RESOLVE_TAC AES128_GCM_DEC_ALT_EXEC (200--203) THEN
  WB_PT_CAPTURE_TAC "s203" `Q12` `cph0:int128` `ctr0:int128` THEN
  ARM_STEPS_RESOLVE_Q30_TAC AES128_GCM_DEC_ALT_EXEC (204--247) THEN
  (* s248 = st1 {v12.16b},[x2],#16 (block-0 store); carry the readback across the discard *)
  ARM_VSTEPS_FOLD_TAC AES128_GCM_DEC_ALT_EXEC [248] THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 out_p) s248` with _ -> false)
    then MP_TAC th else NO_TAC) THEN
  DISCARD_OLDSTATE_KEEPGH_TAC "s248" THEN DISCH_TAC THEN
  ARM_STEPS_FOLD_KEEPGH_TAC AES128_GCM_DEC_ALT_EXEC (249--260) THEN
  WB_PT_CAPTURE_TAC "s260" `Q12` `cph1:int128` `gcm_ctr_inc ctr0:int128` THEN
  ARM_STEPS_FOLD_KEEPGH_TAC AES128_GCM_DEC_ALT_EXEC (261--272) THEN
  (* s273 = st1 {v12.16b},[x2] (block-1 store); carry both readbacks across the discard *)
  ARM_VSTEPS_TAC AES128_GCM_DEC_ALT_EXEC [273] THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 (word_add out_p (word 16))) s273` with _ -> false)
    then MP_TAC th else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 out_p) s273` with _ -> false)
    then MP_TAC th else NO_TAC) THEN
  DISCARD_OLDSTATE_KEEPGH_TAC "s273" THEN DISCH_TAC THEN DISCH_TAC THEN
  ARM_STEPS_FOLD_KEEPGH_TAC AES128_GCM_DEC_ALT_EXEC (274--285) THEN
  (* GHASH bridge at s285 (pc+3736, after eor3 v19,v19,v18,v17) *)
  WB_REPLACE_READ_TAC `read Q19 (s285:armstate)` WB2_GMULT2_BITBLAST_TAC
    `ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1]` THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      [word_bytereverse cph0; word_bytereverse cph1]` THEN
  (* 286 ext (half-swap), 287 rev64 -> Q19 = word_bytereverse gval *)
  ARM_VSTEPS_FOLD_TAC AES128_GCM_DEC_ALT_EXEC (286--287) THEN
  WB_REPLACE_READ_TAC `read Q19 (s287:armstate)` (CONV_TAC WORD_BLAST)
    `word_bytereverse (gval:int128)` THEN
  (* 288 = st1 {v19.16b},[x3] (tag store); 289/290 = rev32 v30, str q30,[x16] *)
  ARM_VSTEPS_TAC AES128_GCM_DEC_ALT_EXEC [288] THEN
  ARM_VSTEPS_FOLD_TAC AES128_GCM_DEC_ALT_EXEC (289--290) THEN
  DISCARD_COUNTER_ONLY_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
  [ivtac;
   REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
   REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[]];;

(* The shared back-legs, proved once per residue; hyps = 0 audits the     *)
(* five dropped seam cells and the generic X9.                           *)
let WB_TAIL_GEN2_1 = prove(wbn_tail_backleg_goal5_return 1,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 1 THEN WB_TAIL_1_TAC (WB_IVEC_CLOSE_TAC 1));;
let WB_TAIL_GEN2_2 = prove(wbn_tail_backleg_goal5_return 2,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 2 THEN WB_TAIL_2_TAC (WB_IVEC_CLOSE_TAC 2));;

(* The band prover, for k = 5..8 (bands 1..4 take the 1-4 block path, after  *)
(* wbn_backlegs below): split at the seam pc+3032 via FRAME_SUBSUMED +        *)
(* TRANS, discharge the front leg with WB_FRONT_BUF, and the back leg (not    *)
(* re-simulated) from the back-leg theorem by precondition weakening (q_at k  *)
(* implies the 5-cell-dropped weak precondition).                             *)
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

(* ------------------------------------------------------------------------- *)
(* The N >= 3 band machinery: pmul-atom merging and the N-block GHASH        *)
(* spec forms (GMULTn_FULL_CORRECT_BA, spec_to_byteform_wbN,                 *)
(* GHASH_POLYVAL_ACC_6..8), and the Q18-latest stepper.                      *)
(* ------------------------------------------------------------------------- *)
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

(* ---- shared merge machinery (MERGE_ANY_TAC, MERGE_QQPAIR_KM_TAC); see the
   WB_8 header note for the greedy-pairing story. ---- *)

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

(* ---- WB_7/WB_8 stepping machinery.
   Keeping all of Q16-Q19 alive across the ~130 states of the stores window
   (ARM_STEPS_FOLD_KEEPGH_TAC) makes the per-step GCM_SIMD_SIMPLIFY pass
   rescan a linearly growing pile, O(n^2) overall.  Instead, step the window
   keeping ONLY the LATEST read Q18 fact (the machine's carried GHASH mid;
   store readbacks self-propagate), atomize it as `midacc`, and let the
   bridge expand it once. ---- *)
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
(* The per-step normalizer is GCM_SIMD_SIMPLIFY_CORE_TAC, NOT the double-pass
   GCM_SIMD_SIMPLIFY_TAC (= CORE THEN CORE).  The second CORE pass is a full
   RULE_ASSUM traversal of the whole carried GHASH pile; on the tail sim it is
   a no-op on 114/122 steps (it only folds the fresh REV64 byte-tree at the ~8
   block-boundary steps, and that fold is re-done downstream by the Q19
   bridge's WORD_BYTEREVERSE_REVERSEFIELDS/RF8_SUBWORD rewrites).  If a future
   edit needs the fixpoint here, restore GCM_SIMD_SIMPLIFY_TAC. *)
let ARM_STEPS_FOLD_Q18LATEST_TAC exec snums =
  MAP_EVERY (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN GCM_SIMD_SIMPLIFY_CORE_TAC THEN
              DISCARD_STALE_Q18_TAC THEN DISCARD_OLDSTATE_KEEPQ18_TAC s THEN CLARIFY_TAC)
    (statenames "s" snums);;
(* Merge variants that unfold karatsuba_mid inside the
   closing WORD_BLAST: the midacc expansion exposes machine mids whose spec
   partners are karatsuba_mid-folded. *)
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
(* WA-unify via BITBLAST_RULE: stock WA_UNIFY_TAC's WORD_RULE stack-overflows
   on the ~1.1k-char wa inputs this state produces. *)
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
   normalizer (GCM_SIMD_SIMPLIFY_CORE_TAC + EXT8_LANE0_IS_SUBWORD_HI) collapses
   the ext-form Karatsuba-mid lanes to the plain lanes, but the qq
   numbers ABBREV_INNER_PMULS assigns are not stable across bands.  So this
   pairs the leftover mid pmuls by H-power (which keys off the KEY operand
   h2/h3/.., unaffected by the data-side ext form): after MERGE_ANY_TAC has
   merged everything it can, the only residual mismatch is a set of
   karatsuba-mid qq atoms UNIQUE to the LHS vs UNIQUE to the RHS; each
   LHS-unique qq merges with the RHS-unique qq of the SAME H-power
   (MERGE_QQPAIR_KM_TAC, closed by WORD_BLAST, so it is form-insensitive). *)
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

(* WB_7/WB_8 midacc bridges leave a stray zero limb in each 64-bit lane
   (from the carried mid entering the reduce as word 0 xor ...):
   collapse it before the bubble sort, then finish as LANE_FINISH_TAC. *)
let ZSUB0 = prove(`word_subword (word 0:int128) (0,64):64 word = word 0`, CONV_TAC WORD_BLAST);;
let ZSUB0b = prove(`word_subword (word 0:int128) (64,64):64 word = word 0`, CONV_TAC WORD_BLAST);;
let LANE_FINISH_Z_TAC : tactic =
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  CONV_TAC(RAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[SJ_COLLAPSE; SJ_COLLAPSE2] THEN REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[ZSUB0; ZSUB0b; WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  CONV_TAC(BINOP_CONV bubble_fix) THEN REFL_TAC;;

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

(* ============================================================================
   WB_6BLOCK machinery.  GHASH_POLYVAL_ACC_6 is proved here from
   GHASH_POLYVAL_ACC_BATCHED with the same recipe as the 3..5-block forms in
   the N-block GHASH Karatsuba layer above.
   ============================================================================ *)
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

(* ============================================================================
   WB_7BLOCK machinery (ACC_7 proved from BATCHED like ACC_6 above).
   ============================================================================ *)
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

(* ============================================================================
   WB_8BLOCK machinery.

   MERGE NOTE: at N=8 the stock MERGE_2BLK_TAC mis-pairs the qq atoms -- its
   find_pair takes the FIRST signature-compatible candidate, and at N=8 that
   greedy choice pairs machine-lo with spec-hi atoms, leaving 4 unmergeable
   leftovers.  MERGE_ONE_ANY_TAC uses the same pairing signature but tries
   ALL candidate pairs via FIRST (backtracking on the WORD_BLAST operand
   close), so a bad greedy pick self-corrects.
   ============================================================================ *)
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

(* A GF(2)-linear 128-bit word identity over pmul atoms, closed without bit- *)
(* blasting the big terms: split into the two 64-bit lanes, push subword,    *)
(* zx and shl through every xor, generalize each distinct xor leaf (largest  *)
(* first) to a fresh 64-bit variable, and decide the remaining pure-xor      *)
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

(* Put back the reduction-constant pmul atoms and turn every                *)
(* word_pmul x (word 0xC2..) into its shift form (PMUL_W_64_128).           *)
let EXPAND_WPMUL_ATOMS_TAC : tactic = fun (asl,w) ->
  let defs = filter (fun (_,th) -> let c = concl th in
    is_eq c && is_var(rhs c) && isWpmul(lhs c)) asl in
  REWRITE_TAC (map (GSYM o snd) defs) (asl,w);;

(* The 3-block GHASH bridge: T's spec unfolding and pmul-atom merges (with  *)
(* the midacc expansion between the two merge rounds), then the reduction    *)
(* constant pmuls linearized, the remaining data pmuls merged once more, and *)
(* the GF(2)-linear rest closed lane by lane.                                *)
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
  (* GHASH bridge at s296 (pc+3736, after eor3 v19,v19,v18,v17) *)
  WB_REPLACE_READ_TAC `read Q19 (s296:armstate)` WB3_GMULT3_BRIDGE_TAC
    `ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2]` THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2]` THEN
  (* 297 ext (half-swap), 298 rev64 -> Q19 = word_bytereverse gval *)
  ARM_VSTEPS_FOLD_TAC AES128_GCM_DEC_ALT_EXEC (297--298) THEN
  WB_REPLACE_READ_TAC `read Q19 (s298:armstate)` (CONV_TAC WORD_BLAST)
    `word_bytereverse (gval:int128)` THEN
  (* 299 = st1 {v19.16b},[x3] (tag store); 300/301 = rev32 v30, str q30,[x16] *)
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
(* pmul is left: each round drops the lanes no instruction reads             *)
(* (WB_MID_FIX), then abbreviates and merges the innermost pmuls, so a pmul  *)
(* nested in another's operand is merged in a later round.                  *)
let MERGE_ALL_PMULS_TAC : tactic =
  let is_pmul_app t = try let (h,args) = strip_comb t in
        fst(dest_const h) = "word_pmul" && length args = 2 with _ -> false in
  REPEAT (W(fun (_,w) ->
    if can (find_term is_pmul_app) w
    then REWRITE_TAC WB_MID_FIX THEN ABBREV_INNER_PMULS_TAC THEN AUTO_MERGE_MIDS_KM_TAC
    else NO_TAC));;

(* The N-block GHASH bridge (N >= 3), WB3_GMULT3_BRIDGE_TAC generalized:     *)
(* GMULTN_FULL_CORRECT_BA instantiated at the block pairing T uses           *)
(* (block 0 with H^N, block i with H^(N-i)), spec_to_byteform_wbN fed the    *)
(* h2..hN abbreviation facts.                                                *)
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

(* The tail for residue n >= 3 from the seam s199, driven by its step map:  *)
(* `taken` is the taken b.gt (r = 8: the first, into the exact-8 drain),    *)
(* `pts` the (state, block) pairs of the plaintext eor3s after block 0's at *)
(* s203, `ex` the exit state; the reduction is the 8 steps ex-12 .. ex-5    *)
(* (0xe78 .. 0xe94), with the mid accumulator named at ex-13.               *)
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

(* r = 5..8 through WB_TAIL_N_TAC, from the step map (states from the seam   *)
(* s199): the cascade's taken b.gt, the plaintext eor3 of blocks 1..r-1 and  *)
(* the exit state (after the ivec store at 0xea8).                            *)
(*   r = 5: b.gt s231 (0xc54); eor3 s242 s258 s276 s290; exit s320.          *)
(*   r = 6: b.gt s224 (0xc38); eor3 s230 s250 s266 s284 s298; exit s328.     *)
(*   r = 7: b.gt s216 (0xc18); eor3 s230 s236 s256 s272 s290 s304; exit s334. *)
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

(* r = 8 takes the first b.gt (0xbe8) to the exact-8 drain (0xecc), so      *)
(* there is no `sub v30`: Q30 is still gcm_ctr_raw (word 8) ctr0 at the     *)
(* ivec write-back, and WB_IVEC_CLOSE_TAC 8's sub_chain rewrites would be   *)
(* the looping x = word_sub x (word 0).  The same close without them.       *)
(* That path also skips the movi zeroing of v17/v18/v19; its                *)
(* `ext v18.16b,v24.16b,v24.16b,#8` (s207) overwrites the seam's            *)
(* unconstrained Q18 whole, and the pmull at s215 reads only its lane 0.    *)
(* The drain (s205-s297) feeds the partial tag into its first block only,   *)
(* defers three blocks' products to v13-v15 and folds each into the next    *)
(* block's accumulations with eor3, and rejoins the cascade at reduce       *)
(* (0xe70) by the `b` at s297.  The 8-block GHASH bridge closes it          *)
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

(* The back-legs by residue, for the shifted-tail recompositions (k-1 index). *)
let wbn_backlegs =
  [WB_TAIL_GEN2_1; WB_TAIL_GEN2_2; WB_TAIL_GEN2_3; WB_TAIL_GEN2_4;
   WB_TAIL_GEN2_5; WB_TAIL_GEN2_6; WB_TAIL_GEN2_7; WB_TAIL_GEN2_8];;

(* ========================================================================= *)
(* The 1-4 block path.  For nblk <= 4 the b.le at 0x38 (step 8) branches to  *)
(* w5r_small (0x1040), which loads the counter, the tag and the 11 round     *)
(* keys and dispatches on x9 to stub_k.  stub_k seeds the GHASH accumulator  *)
(* with Xi' * H^k and enters the chain g_k, .., g1 at g_k: each group        *)
(* decrypts one block and folds its ciphertext into the accumulator with     *)
(* the matching power of H; g1 also reduces, stores the tag, the counter and *)
(* the last plaintext block, and branches to frame_restore (0xeac, pc+3756), *)
(* the core exit.  WB_FUSED_kBLOCK (k = 1..4) proves each path from the core *)
(* entry pc+0x1c, and mk_band_from_fused restates it as the band goal        *)
(* mk_band_goal k without re-simulation.                                     *)
(* The tactic library below is the AES-256 proof's                           *)
(* (aes256_gcm_dec_alt.ml), but for the k = 1 bridge: there                  *)
(* BRIDGE_CLOSE_FULL_TAC with its own lane finisher, here BRIDGE_CLOSE_1_TAC *)
(* on the k >= 2 bridges' BRIDGE_FINISH_TAC (factored out of                 *)
(* DEC_BRIDGE_ROUTEB_TAC).                                                   *)
(* ========================================================================= *)

(* ---- state-discard helper that keeps the GHASH accumulator regs + htbl loads ---- *)
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

(* ---- Q-scoped, FIXPOINT-MEMOIZED per-step SIMD normalizer ----
   Same three rewrite passes as the shared GCM_SIMD_SIMPLIFY_CORE_TAC (lemmas.ml),
   but applied ONLY to `read Qn s = ...` assumptions.  In the KEEPGHALL windows
   the discard KEEPS the full multi-block GHASH accumulator history, so the pile
   grows to ~400-1000 assumptions of which ~215 are memory reads, ~22
   nonoverlapping and the rest non-Q / flags -- none of which the SIMD rules (REV64 lanes
   / WORD_SWAP_HALVES / EXT8_LANE0 / REV32_LANE_SUBWORD) can EVER rewrite.  The Q-scope
   skips those, and the surviving Q-reads are mostly already at a fixpoint of the
   normalizer F.  F's action on an assumption is a PURE function of its conclusion,
   so if F once left a conclusion unchanged it always will.  Memoize the set of concl
   terms already proven to be F-fixpoints (`gcm_simd_fixpt_tbl`): for each Q-read asm,
   if its concl is a known fixpoint skip it (GUARANTEED no-op); else apply F and, if F
   leaves it unchanged, record the fixpoint.  This is BIT-IDENTICAL to always applying
   the Q-scoped F (skipping a proven fixpoint yields exactly F's output) -- it satisfies
   the soundness invariant WITHOUT any current-state approximation.  The table
   accumulates across the 4 fused bodies (CLEAR_KEEPGHALL_MEMO_TAC resets it at each
   body start so every WB_FUSED_kBLOCK `prove` is hermetic); a stale fixpoint could only
   ever be a genuine no-op anyway, so carryover would also be bit-identical.
   Scoped to the fused arc (ARM_STEPS_FOLD_KEEPGHALL_TAC's sole users are
   WB_FUSED_1..4BLOCK); the shared _CORE_TAC is UNCHANGED for the tail/front/mainloop. *)
let gcm_simd_fixpt_tbl : (term,unit) Hashtbl.t = Hashtbl.create 8192;;
let CLEAR_KEEPGHALL_MEMO_TAC : tactic =
  fun (asl,w) -> Hashtbl.clear gcm_simd_fixpt_tbl; ALL_TAC (asl,w);;
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

(* ---- per-window symbolic-execution stepper ----
   MAP_EVERY over the step range: verbose-step, single-pass Q-scoped GCM_SIMD
   normalizer (a second CORE pass is a no-op except on block-boundary REV64
   folds, which the bridge re-does downstream via RF8_SUBWORD), keep-GHALL
   discard, clarify. *)
let ARM_STEPS_FOLD_KEEPGHALL_TAC exec snums =
  MAP_EVERY (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN GCM_SIMD_SIMPLIFY_CORE_QSCOPED_TAC THEN
              DISCARD_OLDSTATE_KEEPGHALL_TAC s THEN DISCARD_STALE_TAC s THEN CLARIFY_TAC)
    (statenames "s" snums);;

(* ---- ctr0 rebuild: the byte-shuffled reconstruction of the 128-bit counter ---- *)
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

(* ---- collapse a Q-register's accumulator chain self-contained at state st ---- *)
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

(* ---- DEC_BRIDGE_ROUTEB_TAC: the parameterised bridge close for k>=2 ----
   For k>=2 the per-k bridge closes (BRIDGE_CLOSE_{2,3,4}_CPH*_TAC, thin wrappers
   below) share one prelude + finisher and differ ONLY in the spec-equation `spec_eq` and the
   three karatsuba-mid qq-distribution identities the machine (LHS, DISTRIBUTED) needs
   to match the spec (RHS, GMULTk byteform, COMBINED).  Two of the three are "LAND-shape"
   (subword-level, CONJUNCT1 WORD_PMUL_XOR + WORD_XOR_ACI) and one is "MID-shape"
   (nested subword(join..) operands, GSYM CONJUNCT1 + PMUL_CONG_128 + WORD_BLAST).
   The caller passes sN, the pre-built spec_eq (from its own spec_to_byteform_wbK /
   dec_bridge_specl / GMULTk_FULL_CORRECT_BA + h-assumptions), and the (lo,hi,mid) triples. *)
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

(* ---- the k=1 bridge: the machine's seed and block products fold pairwise ---- *)
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

(* BRIDGE_CLOSE_1_TAC: nblk=1, the bridge close at the reduce s<sN>.  The tag's
   ghash_polyval_acc over one block is polyval_dot (xi (+) cph) H
   (GHASH_1BLOCK_CORRECT), in GMULT_FULL_CORRECT_BA's byte form.  Where the k>=2
   bridges distribute the spec's products (DEC_BRIDGE_ROUTEB_TAC's qq triples),
   here the machine's seed and block products fold pairwise into the spec's:
   FOLD_LANE (either 64-bit lane) in the rewrite, FOLD_MID2 on the abbreviated
   mid terms.  The close is the k>=2 bridges' BRIDGE_FINISH_TAC. *)
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

(* nblk = 1: 87 steps from the core entry pc+0x1c to the core exit pc+3756: *)
(* s1-s8 the front and the dispatch (the b.le at s8 is taken), s9-s27       *)
(* w5r_small (counter, tag and round-key loads and the x9 compares), s28-s35 *)
(* stub_1 (the seed Xi' * H), s36-s86 g1 (the AES-128 tower, the reduced     *)
(* GHASH at s78, the tag store at s81, the counter store at s84, the         *)
(* plaintext eor3 at s85 and its store at s86), s87 the b to frame_restore. *)
let fused1_goal =
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    cph xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 h hk.
    aligned 16 stackpointer /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (out_p:int64, 16) /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (xi_p:int64, 16) /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (ivec_p:int64, 16) /\
    nonoverlapping (out_p, 16) (xi_p, 16) /\
    nonoverlapping (out_p, 16) (ivec_p, 16) /\
    nonoverlapping (xi_p, 16) (ivec_p, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 16) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 176) /\
    nonoverlapping (ivec_p, 16) (htbl_p:int64, 192) /\
    nonoverlapping (in_p, 16) (stackpointer, 80) /\
    nonoverlapping (key_p, 176) (stackpointer, 80) /\
    nonoverlapping (htbl_p, 192) (stackpointer, 80) /\
    nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
    nonoverlapping (xi_p, 16) (in_p, 16) /\
    nonoverlapping (xi_p, 16) (key_p, 176) /\
    nonoverlapping (xi_p, 16) (htbl_p, 192) /\
    nonoverlapping (xi_p, 16) (stackpointer, 80) /\
    nonoverlapping (out_p, 16) (in_p, 16) /\
    nonoverlapping (out_p, 16) (key_p, 176) /\
    nonoverlapping (out_p, 16) (htbl_p, 192) /\
    nonoverlapping (out_p, 16) (stackpointer, 80) /\
    word_subword hk (0,64) :64 word =
      word_xor (word_subword h (0,64):64 word) (word_subword h (64,64):64 word)
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
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
          read (memory :> bytes128 htbl_p) s = h /\
          read (memory :> bytes128 (word_add htbl_p (word 16))) s = hk)
     (\s. read PC s = word (pc + 3756) /\
          read X9 s = word 16 /\
          read (memory :> bytes128 out_p) s =
          word_xor cph (aes128_encrypt ctr0 [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10]) /\
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
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`;;

let WB_FUSED_1BLOCK = prove(fused1_goal,
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              WB_MC_LEN] THEN
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN CLEAR_KEEPGHALL_MEMO_TAC THEN
  (* the 64-bit halves of the 128-bit reads, for the ldr d25 of hk *)
  MEMORY_SPLIT_TAC 1 THEN
  (* The windows: the front, w5r_small and stub_1, then g1 up to the reduce. *)
  (* Each ends with the accumulator registers made self-contained, so the    *)
  (* older states can be discarded.  The plaintext store needs no cut-point: *)
  (* the close proves the block at s87.                                      *)
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

(* BRIDGE_CLOSE_2_CPH1_TAC: nblk=2, cph1 specl.  Thin wrapper over the
   shared DEC_BRIDGE_ROUTEB_TAC; builds spec_eq from the k=2-local
   spec_to_byteform_2 / dec_bridge_specl_2_cph1 / GMULT2_FULL_CORRECT_BA, and passes the k=2
   block-0 (H^2) karatsuba-mid distributions: qq8=qq1(+)qq5 (hi), qq7=qq0(+)qq4 (lo),
   qq12=qq9(+)qq10 (mid). *)
let BRIDGE_CLOSE_2_CPH1_TAC sN : tactic = fun (asl,w) ->
  let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
  let gmult_dec = REWRITE_RULE[LET_DEF;LET_END_DEF] (SPECL dec_bridge_specl_2_cph1 GMULT2_FULL_CORRECT_BA) in
  let spec_eq = TRANS (MP spec_to_byteform_2 h2asm) (GSYM gmult_dec) in
  DEC_BRIDGE_ROUTEB_TAC sN spec_eq
    (("qq8","qq1","qq5"),("qq7","qq0","qq4"),("qq12","qq9","qq10")) (asl,w);;

(* nblk = 2: 123 steps: s1-s28 the front, the dispatch and w5r_small, s29-  *)
(* s36 stub_2 (the seed Xi' * H^2), s37-s71 g2 (block 0, folded with H^2,  *)
(* stored at s71), s72-s123 g1 (block 1, the reduce at s114, then the tag,  *)
(* counter and block-1 stores) and the b to frame_restore.                   *)
let fused2_goal =
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    cph0 cph1 xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 h hk h2.
    aligned 16 stackpointer /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (out_p:int64, 32) /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (xi_p:int64, 16) /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (ivec_p:int64, 16) /\
    nonoverlapping (out_p, 32) (xi_p, 16) /\
    nonoverlapping (out_p, 32) (ivec_p, 16) /\
    nonoverlapping (xi_p, 16) (ivec_p, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 32) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 176) /\
    nonoverlapping (ivec_p, 16) (htbl_p:int64, 192) /\
    nonoverlapping (in_p, 32) (stackpointer, 80) /\
    nonoverlapping (key_p, 176) (stackpointer, 80) /\
    nonoverlapping (htbl_p, 192) (stackpointer, 80) /\
    nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
    nonoverlapping (xi_p, 16) (in_p, 32) /\
    nonoverlapping (xi_p, 16) (key_p, 176) /\
    nonoverlapping (xi_p, 16) (htbl_p, 192) /\
    nonoverlapping (xi_p, 16) (stackpointer, 80) /\
    nonoverlapping (out_p, 32) (in_p, 32) /\
    nonoverlapping (out_p, 32) (key_p, 176) /\
    nonoverlapping (out_p, 32) (htbl_p, 192) /\
    nonoverlapping (out_p, 32) (stackpointer, 80) /\
    word_subword hk (0,64) :64 word =
      word_xor (word_subword h (0,64):64 word) (word_subword h (64,64):64 word) /\
    word_subword hk (64,64) :64 word =
      word_xor (word_subword h2 (0,64):64 word) (word_subword h2 (64,64):64 word) /\
    byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h)
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
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
          read (memory :> bytes128 htbl_p) s = h /\
          read (memory :> bytes128 (word_add htbl_p (word 16))) s = hk /\
          read (memory :> bytes128 (word_add htbl_p (word 32))) s = h2)
     (\s. read PC s = word (pc + 3756) /\
          read X9 s = word 32 /\
          read (memory :> bytes128 out_p) s =
          word_xor cph0 (aes128_encrypt ctr0 [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10]) /\
          read (memory :> bytes128 (word_add out_p (word 16))) s =
          word_xor cph1 (aes128_encrypt (gcm_ctr_inc ctr0) [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10]) /\
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
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`;;

let WB_FUSED_2BLOCK = prove(fused2_goal,
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              WB_MC_LEN] THEN
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN CLEAR_KEEPGHALL_MEMO_TAC THEN
  (* the 64-bit halves of the 128-bit reads, for the ldr d25 of hk *)
  MEMORY_SPLIT_TAC 1 THEN
  (* The windows: the front, w5r_small and stub_2, then g2 and g1.  Each     *)
  (* ends with the accumulator registers made self-contained, so the older   *)
  (* states can be discarded.  The plaintext stores need no cut-point: the   *)
  (* close proves both blocks at s123.                                       *)
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


(* cph2 last-block specl (mirror k=2's dec_bridge_specl_2_cph1) *)
let dec_bridge_specl_3_cph2 =
  [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h3:int128`;
   `word_bytereverse cph1:int128`; `byteswap128 h2:int128`;
   `word_bytereverse cph2:int128`; `byteswap128 h:int128`];;

(* BRIDGE_CLOSE_3_CPH2_TAC: nblk=3, last block cph2.  Thin wrapper over the
   shared DEC_BRIDGE_ROUTEB_TAC; the 3 block-0(H^3) mid distributions:
   qq11=qq1(+)qq7 (hi), qq10=qq0(+)qq6 (lo), qq16=qq12(+)qq13 (mid). *)
let BRIDGE_CLOSE_3_CPH2_TAC sN : tactic = fun (asl,w) ->
  let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
  let h3asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h3` with _->false) asl) in
  let gmult_dec = REWRITE_RULE[LET_DEF;LET_END_DEF] (SPECL dec_bridge_specl_3_cph2 GMULT3_FULL_CORRECT_BA) in
  let spec_eq = TRANS (MP spec_to_byteform_wb3 (CONJ h2asm h3asm)) (GSYM gmult_dec) in
  DEC_BRIDGE_ROUTEB_TAC sN spec_eq
    (("qq11","qq1","qq7"),("qq10","qq0","qq6"),("qq16","qq12","qq13")) (asl,w);;

(* nblk = 3: 157 steps: s1-s27 the front, the dispatch and w5r_small, s28-  *)
(* s35 stub_3 (the seed Xi' * H^3), s36-s70 g3, s71-s105 g2 (blocks 0 and 1, *)
(* stored at s70 and s105), s106-s157 g1 (block 2, the reduce at s148, then  *)
(* the tag, counter and block-2 stores) and the b to frame_restore.          *)
let fused3_goal =
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    cph0 cph1 cph2 xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 h hk h2 h3 h3k.
    aligned 16 stackpointer /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (out_p:int64, 48) /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (xi_p:int64, 16) /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (ivec_p:int64, 16) /\
    nonoverlapping (out_p, 48) (xi_p, 16) /\
    nonoverlapping (out_p, 48) (ivec_p, 16) /\
    nonoverlapping (xi_p, 16) (ivec_p, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 48) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 176) /\
    nonoverlapping (ivec_p, 16) (htbl_p:int64, 192) /\
    nonoverlapping (in_p, 48) (stackpointer, 80) /\
    nonoverlapping (key_p, 176) (stackpointer, 80) /\
    nonoverlapping (htbl_p, 192) (stackpointer, 80) /\
    nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
    nonoverlapping (xi_p, 16) (in_p, 48) /\
    nonoverlapping (xi_p, 16) (key_p, 176) /\
    nonoverlapping (xi_p, 16) (htbl_p, 192) /\
    nonoverlapping (xi_p, 16) (stackpointer, 80) /\
    nonoverlapping (out_p, 48) (in_p, 48) /\
    nonoverlapping (out_p, 48) (key_p, 176) /\
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
     (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
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
          read (memory :> bytes128 htbl_p) s = h /\
          read (memory :> bytes128 (word_add htbl_p (word 16))) s = hk /\
          read (memory :> bytes128 (word_add htbl_p (word 32))) s = h2 /\
          read (memory :> bytes128 (word_add htbl_p (word 48))) s = h3 /\
          read (memory :> bytes128 (word_add htbl_p (word 64))) s = h3k)
     (\s. read PC s = word (pc + 3756) /\
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
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`;;

let WB_FUSED_3BLOCK = prove(fused3_goal,
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              WB_MC_LEN] THEN
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN CLEAR_KEEPGHALL_MEMO_TAC THEN
  (* the 64-bit halves of the 128-bit reads, for the ldr d25 of hk and h3k *)
  MEMORY_SPLIT_TAC 1 THEN
  (* The windows: the front, w5r_small and stub_3, then g3 .. g1.  Each ends *)
  (* with the accumulator registers made self-contained, so the older states *)
  (* can be discarded.  The plaintext stores need no cut-point: the close    *)
  (* proves all three blocks at s157.                                        *)
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


let dec_bridge_specl_4_cph3 =
  [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h4:int128`;
   `word_bytereverse cph1:int128`; `byteswap128 h3:int128`;
   `word_bytereverse cph2:int128`; `byteswap128 h2:int128`;
   `word_bytereverse cph3:int128`; `byteswap128 h:int128`];;

(* BRIDGE_CLOSE_4_CPH3_TAC: nblk=4, last block cph3.  Thin wrapper over the shared
   DEC_BRIDGE_ROUTEB_TAC; the 3 block-0(H^4) mid distributions:
   qq14=qq9(+)qq1 (hi), qq13=qq8(+)qq0 (lo), qq20=qq15(+)qq16 (mid). *)
let BRIDGE_CLOSE_4_CPH3_TAC sN : tactic = fun (asl,w) ->
  let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
  let h3asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h3` with _->false) asl) in
  let h4asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h4` with _->false) asl) in
  let gmult_dec = REWRITE_RULE[LET_DEF;LET_END_DEF] (SPECL dec_bridge_specl_4_cph3 GMULT4_FULL_CORRECT_BA) in
  let spec_eq = TRANS (MP spec_to_byteform_wb4 (CONJ h2asm (CONJ h3asm h4asm))) (GSYM gmult_dec) in
  DEC_BRIDGE_ROUTEB_TAC sN spec_eq
    (("qq14","qq9","qq1"),("qq13","qq8","qq0"),("qq20","qq15","qq16")) (asl,w);;

(* nblk = 4: 193 steps: s1-s28 the front, the dispatch and w5r_small, s29-  *)
(* s36 stub_4 (the seed Xi' * H^4), s37-s71 g4, s72-s106 g3, s107-s141 g2    *)
(* (blocks 0..2, stored at s71, s106 and s141), s142-s193 g1 (block 3, the   *)
(* reduce at s184, then the tag, counter and block-3 stores) and the b to    *)
(* frame_restore.                                                            *)
let fused4_goal =
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    cph0 cph1 cph2 cph3 xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 h hk h2 h3 h3k h4.
    aligned 16 stackpointer /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (out_p:int64, 64) /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (xi_p:int64, 16) /\
    nonoverlapping (word pc, LENGTH aes128_gcm_dec_alt_tmc) (ivec_p:int64, 16) /\
    nonoverlapping (out_p, 64) (xi_p, 16) /\
    nonoverlapping (out_p, 64) (ivec_p, 16) /\
    nonoverlapping (xi_p, 16) (ivec_p, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 64) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 176) /\
    nonoverlapping (ivec_p, 16) (htbl_p:int64, 192) /\
    nonoverlapping (in_p, 64) (stackpointer, 80) /\
    nonoverlapping (key_p, 176) (stackpointer, 80) /\
    nonoverlapping (htbl_p, 192) (stackpointer, 80) /\
    nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
    nonoverlapping (xi_p, 16) (in_p, 64) /\
    nonoverlapping (xi_p, 16) (key_p, 176) /\
    nonoverlapping (xi_p, 16) (htbl_p, 192) /\
    nonoverlapping (xi_p, 16) (stackpointer, 80) /\
    nonoverlapping (out_p, 64) (in_p, 64) /\
    nonoverlapping (out_p, 64) (key_p, 176) /\
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
     (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
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
          read (memory :> bytes128 htbl_p) s = h /\
          read (memory :> bytes128 (word_add htbl_p (word 16))) s = hk /\
          read (memory :> bytes128 (word_add htbl_p (word 32))) s = h2 /\
          read (memory :> bytes128 (word_add htbl_p (word 48))) s = h3 /\
          read (memory :> bytes128 (word_add htbl_p (word 64))) s = h3k /\
          read (memory :> bytes128 (word_add htbl_p (word 80))) s = h4)
     (\s. read PC s = word (pc + 3756) /\
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
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`;;

let WB_FUSED_4BLOCK = prove(fused4_goal,
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              WB_MC_LEN] THEN
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN CLEAR_KEEPGHALL_MEMO_TAC THEN
  (* the 64-bit halves of the Karatsuba table entries hk and h3k *)
  MAP_EVERY (fun v -> FIRST_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 1) o
    check (fun th -> rand(concl th) = v))) [`hk:int128`; `h3k:int128`] THEN
  ARM_STEPS_TAC AES128_GCM_DEC_ALT_EXEC (1--36) THEN
  (* The windows g4 .. g1: each ends with the accumulator registers made     *)
  (* self-contained, so the older states can be discarded.  The plaintext    *)
  (* stores need no cut-point: the close proves all four blocks at s193.     *)
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

(* The bridge to the band goals: WB_FUSED_kBLOCK's postcondition and frame   *)
(* are mk_band_goal k's under cph_i := bytes_to_int128 (SUB_LIST (16 * i,16) *)
(* ibytes); only the precondition differs (the whole-buffer read and         *)
(* htable_mem_dec there, the per-block reads and explicit table slots here), *)
(* bridged by INPUT_BYTES_TO_BYTE128_LANES and the htable_mem_dec unfold.     *)
(* The fused theorems' hk, h2 .. h4 side conditions discharge by             *)
(* HK_LOW/HI_IS_KARA, karatsuba_mid and BYTESWAP128_INVOLUTION.              *)
let HK_LOW_IS_KARA = prove
 (`!a b:64 word. word_subword (word_join a b:int128) (0,64):64 word = b`,
  CONV_TAC WORD_BLAST);;
let HK_HI_IS_KARA = prove
 (`!a b:64 word. word_subword (word_join a b:int128) (64,64):64 word = a`,
  CONV_TAC WORD_BLAST);;

(* h-power tower matching htable_mem_dec's internal lets (hb=byteswap128 h;
   h2=byteswap128(polyval_dot hb hb); h3,h4 one more dot each). *)
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


(* Bands 1..4 take the 1-4 block path, so they come from the fused theorems; *)
(* prove_band (the front through WB_FRONT_BUF) needs 5 <= nblk.             *)
let AES128_GCM_DEC_ALT_BUF_1BLOCK = mk_band_from_fused 1 WB_FUSED_1BLOCK;;
let AES128_GCM_DEC_ALT_BUF_2BLOCK = mk_band_from_fused 2 WB_FUSED_2BLOCK;;
let AES128_GCM_DEC_ALT_BUF_3BLOCK = mk_band_from_fused 3 WB_FUSED_3BLOCK;;
let AES128_GCM_DEC_ALT_BUF_4BLOCK = mk_band_from_fused 4 WB_FUSED_4BLOCK;;

(* ------------------------------------------------------------------------- *)
(* The readable band theorems + the <=8-block dispatch theorem.               *)
(* Sim-free from the BUF band theorems: only the input/output presentations   *)
(* change, discharged by ARM-free bridges via ENSURES_PRE/POSTCONDITION_THM.  *)
(* The bridges come in two internal layers (neither is a named spec):         *)
(*   1. byte_list_at plumbing (BYTE_LIST_AT_TO_READ_BYTES /                   *)
(*      BYTE_LIST_AT_WHOLE_CTR / prove_wb_wrapper): per-block stores +        *)
(*      explicit ghash_polyval_acc -> gcm_dec128_pt_bytes /                  *)
(*      gcm_dec_final_xi.                                                    *)
(*   2. NIST vocabulary (htable_mem_8 / GCM_DEC_FINAL_XI_NIST /              *)
(*      nist_input_block_bytes): twisted-key POLYVAL objects -> SP 800-38D  *)
(*      nist_ghash under the free NIST hash key H with                       *)
(*      byteswap128 h = ghash_twist H.                                       *)
(* The eight AES128_GCM_DEC_ALT_{1..8}BLOCK statements below are written    *)
(* out literally -- they ARE the specification document.  The valid lengths   *)
(* bit_len = 128*nblk (1<=nblk<=8) go to DISPATCH; the reject path for the    *)
(* others (ret 0, no memory) is proved in the exported subroutine theorem.    *)
(* ------------------------------------------------------------------------- *)

(* ---- step 1: input bridge (byte_list_at -> whole-buffer bytes read) -------- *)
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
   (EL_INT128_LIST_TO_BYTES), read off that block's bytes128 store
   (BYTE8_OF_BYTES128); the input-side mirror is WBN_INPUT_ASSEMBLE. *)
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

(* ---- step 3: per-band EL facts builder (generalizes the hand AES_CTR_k_EL). *)
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

(* ---- step 4: wrapper goal builder + prover ---------------------------------
   Wrapper = BUF band statement with (a) the input buffer read replaced by
   byte_list_at ibytes, (b) the postcondition per-block stores + explicit GHASH
   replaced by gcm_dec128_pt_bytes / gcm_dec_final_xi over the whole buffer.
   Sim-free: PRE via BYTE_LIST_AT_TO_READ_BYTES, POST via BYTE_LIST_AT_WHOLE_CTR
   + the per-band EL facts; the spec unfolds via GCM_DEC_*_WHOLE_k. *)
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
    `read (memory :> bytes128 xi_p) s = gcm_dec_final_xi nnn ibytes xi h` in
  (* ivec: carry the band's counter write-back conjunct through
     the wrapper unchanged (spine form; not part of the byte-list vocab lift). *)
  let ivecpost = mk_ivec_conj k in
  let post' = mk_abs(sv, list_mk_conj [pcc; x9c; outpost; xipost; ivecpost]) in
  list_mk_forall(vars,
    mk_imp(hyps, list_mk_comb(rator(rator(rator ens)), [pre'; post'; frame])));;

let ghash_wholes = [GCM_DEC_GHASH_BLOCKS_WHOLE_1;GCM_DEC_GHASH_BLOCKS_WHOLE_2;
                    GCM_DEC_GHASH_BLOCKS_WHOLE_3;GCM_DEC_GHASH_BLOCKS_WHOLE_4;
                    GCM_DEC_GHASH_BLOCKS_WHOLE_5;GCM_DEC_GHASH_BLOCKS_WHOLE_6;
                    GCM_DEC_GHASH_BLOCKS_WHOLE_7;GCM_DEC_GHASH_BLOCKS_WHOLE_8];;
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

(* ------------------------------------------------------------------------- *)
(* NIST-vocabulary bridge layer (the x4-kernel statement shape).              *)
(*  - htable_mem_8: htable_mem_4-style named memory predicate over h_power    *)
(*    indexing, for the 12-slot aws-lc htable layout (packed karatsuba mids). *)
(*  - GCM_DEC_FINAL_XI_NIST: gcm_dec_final_xi = byte-reversed nist_ghash      *)
(*    under byteswap128 h = ghash_twist H (Gueron Prop 1 via                  *)
(*    NIST_GHASH_IS_POLYVAL from common/ghash_nist_bridge.ml).                *)
(*  - nist_input_block_bytes: the NIST (big-endian) view of input block i of *)
(*    a byte list, with the LIST_OF_SEQ_NIST_INPUT bridges to                 *)
(*    gcm_dec_ghash_blocks.                                                   *)
(*  - wordlist_from_memory key condensation: KEY_READS_FROM_WORDLIST +        *)
(*    RK_ETA_11 relate the abstract rk list to the 11 bytes128 key reads.     *)
(* ------------------------------------------------------------------------- *)

(* ---- karatsuba_mid ignores the byteswap of its argument ------------------- *)
let KARATSUBA_MID_BYTESWAP = prove
 (`!x:int128. karatsuba_mid (byteswap128 x) = karatsuba_mid x`,
  GEN_TAC THEN REWRITE_TAC[karatsuba_mid; byteswap128] THEN
  CONV_TAC WORD_BLAST);;

(* ---- h_power 0..7 unfolded to the explicit left-nested dot chains --------- *)
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

(* ---- htable_mem_dec in h_power form (kills the nested let-towers) --------- *)
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

(* ---- the named htable predicate over the abstract key hk ----------------- *)
(* htable_mem_8 hk ptr s is the shared predicate of aes_gcm_spec.ml, and
   HTABLE_MEM_8_FLAT (aes_gcm_common.ml) states it as 12 flat conjuncts.
   hk is the POLYVAL-side key (byteswap128 of the memory h slot); with
   hk = ghash_twist H this is the exact analogue of the x4 kernels'
   htable_mem_4 (ghash_twist ...) hypothesis, extended to 8 powers /
   12 slots (aws-lc layout with packed karatsuba mids). *)
let HTABLE_MEM_DEC_IS_HTABLE_MEM_8 = prove
 (`!(h:int128) (ptr:int64) (s:armstate).
     htable_mem_dec h ptr s <=> htable_mem_8 (byteswap128 h) ptr s`,
  REWRITE_TAC[HTABLE_MEM_DEC_H_POWER; HTABLE_MEM_8_FLAT]);;


(* ---- the tag spec in nist_ghash vocabulary -------------------------------- *)
(* Our band statements quantify the raw htable h slot; the x4 kernels quantify the
   NIST key H with the twist applied in the hypothesis.  The two are related
   by byteswap128 h = ghash_twist H, under which gcm_dec_final_xi IS a
   byte-reversed nist_ghash (Gueron Prop 1 via NIST_GHASH_IS_POLYVAL). *)
let GCM_DEC_FINAL_XI_NIST = prove
 (`!(H:int128) (h:int128) len x xi.
     byteswap128 h = ghash_twist H
     ==> gcm_dec_final_xi len x xi h =
         word_bytereverse
           (nist_ghash H (word_bytereverse xi)
              (MAP word_bytereverse (gcm_dec_ghash_blocks len x)))`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[gcm_dec_final_xi; NIST_GHASH_IS_POLYVAL]);;

(* ---- the NIST (big-endian) view of input block i --------------------------- *)
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


(* ---- the readable-band prover ----------------------------------------------
   For band k: (1) prove_wb_wrapper k buf_thm gives the internal byte-list
   wrapper over _BUF_kBLOCK; (2) instantiate it at ki := EL i rk,
   h := byteswap128 (ghash_twist H), xi := word_reversefields 8 tag0 and
   rewrite into NIST vocabulary; (3) close the literal statement:
   ALLPAIRS/PAIRWISE/ALL unfold + NONOVERLAPPING_SYM hit the wrapper's
   pairwise hypotheses, RK_ETA_11 folds the EL-list back to rk, and
   ENSURES_PRECONDITION_THM + KEY_READS_FROM_WORDLIST bridge the key reads. *)
let bsw_inv = SPEC `ghash_twist H` BYTESWAP128_INVOLUTION;;
let mk_wrapper_nist k wrapper_thm =
  let winst = SPECL ([`pc:num`;`stackpointer:int64`;`out_p:int64`;`xi_p:int64`;`ivec_p:int64`;
                      `in_p:int64`;`key_p:int64`;`htbl_p:int64`;`ibytes:byte list`;
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
(* THE eight readable band theorems (literal statements; the spec document).  *)
(* Reading guide for N blocks: under the standard ABI/nonoverlapping side     *)
(* conditions, decrypting N whole blocks writes to out_p the CTR keystream    *)
(* XORed onto the input bytes (gcm_dec128_pt_bytes), and replaces the tag at  *)
(* xi_p with the standard SP 800-38D GHASH of the N raw ciphertext blocks     *)
(* folded onto tag0 under the NIST hash key H (both tag values stored         *)
(* little-endian-reversed, as the aws-lc caller keeps them).                  *)
(* ------------------------------------------------------------------------- *)

let AES128_GCM_DEC_ALT_1BLOCK = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 16 /\ LENGTH rk = 11 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,16; xi_p,16; ivec_p,16]
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,16; key_p,176; htbl_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,16; xi_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,16; key_p,176; htbl_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 128; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
               byte_list_at ibytes in_p (word 16) s /\
               read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,11) s = rk /\
               htable_mem_8 (ghash_twist H) htbl_p s)
          (\s. read PC s = word (pc + 3756) /\
               read X9 s = word 16 /\
               byte_list_at (gcm_dec128_pt_bytes 16 ibytes ctr0 rk) out_p (word 16) s /\
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
  WB_READABLE_TAC 1 AES128_GCM_DEC_ALT_BUF_1BLOCK);;

let AES128_GCM_DEC_ALT_2BLOCK = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 32 /\ LENGTH rk = 11 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,32; xi_p,16; ivec_p,16]
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,32; key_p,176; htbl_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,32; xi_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,32; key_p,176; htbl_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 256; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
               byte_list_at ibytes in_p (word 32) s /\
               read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,11) s = rk /\
               htable_mem_8 (ghash_twist H) htbl_p s)
          (\s. read PC s = word (pc + 3756) /\
               read X9 s = word 32 /\
               byte_list_at (gcm_dec128_pt_bytes 32 ibytes ctr0 rk) out_p (word 32) s /\
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
  WB_READABLE_TAC 2 AES128_GCM_DEC_ALT_BUF_2BLOCK);;

let AES128_GCM_DEC_ALT_3BLOCK = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 48 /\ LENGTH rk = 11 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,48; xi_p,16; ivec_p,16]
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,48; key_p,176; htbl_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,48; xi_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,48; key_p,176; htbl_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 384; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
               byte_list_at ibytes in_p (word 48) s /\
               read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,11) s = rk /\
               htable_mem_8 (ghash_twist H) htbl_p s)
          (\s. read PC s = word (pc + 3756) /\
               read X9 s = word 48 /\
               byte_list_at (gcm_dec128_pt_bytes 48 ibytes ctr0 rk) out_p (word 48) s /\
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
  WB_READABLE_TAC 3 AES128_GCM_DEC_ALT_BUF_3BLOCK);;

let AES128_GCM_DEC_ALT_4BLOCK = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 64 /\ LENGTH rk = 11 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,64; xi_p,16; ivec_p,16]
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,64; key_p,176; htbl_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,64; xi_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,64; key_p,176; htbl_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 512; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
               byte_list_at ibytes in_p (word 64) s /\
               read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,11) s = rk /\
               htable_mem_8 (ghash_twist H) htbl_p s)
          (\s. read PC s = word (pc + 3756) /\
               read X9 s = word 64 /\
               byte_list_at (gcm_dec128_pt_bytes 64 ibytes ctr0 rk) out_p (word 64) s /\
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
  WB_READABLE_TAC 4 AES128_GCM_DEC_ALT_BUF_4BLOCK);;

let AES128_GCM_DEC_ALT_5BLOCK = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 80 /\ LENGTH rk = 11 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,80; xi_p,16; ivec_p,16]
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,80; key_p,176; htbl_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,80; xi_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,80; key_p,176; htbl_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 640; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
               byte_list_at ibytes in_p (word 80) s /\
               read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,11) s = rk /\
               htable_mem_8 (ghash_twist H) htbl_p s)
          (\s. read PC s = word (pc + 3756) /\
               read X9 s = word 80 /\
               byte_list_at (gcm_dec128_pt_bytes 80 ibytes ctr0 rk) out_p (word 80) s /\
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
  WB_READABLE_TAC 5 AES128_GCM_DEC_ALT_BUF_5BLOCK);;

let AES128_GCM_DEC_ALT_6BLOCK = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 96 /\ LENGTH rk = 11 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,96; xi_p,16; ivec_p,16]
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,96; key_p,176; htbl_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,96; xi_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,96; key_p,176; htbl_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 768; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
               byte_list_at ibytes in_p (word 96) s /\
               read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,11) s = rk /\
               htable_mem_8 (ghash_twist H) htbl_p s)
          (\s. read PC s = word (pc + 3756) /\
               read X9 s = word 96 /\
               byte_list_at (gcm_dec128_pt_bytes 96 ibytes ctr0 rk) out_p (word 96) s /\
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
  WB_READABLE_TAC 6 AES128_GCM_DEC_ALT_BUF_6BLOCK);;

let AES128_GCM_DEC_ALT_7BLOCK = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 112 /\ LENGTH rk = 11 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,112; xi_p,16; ivec_p,16]
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,112; key_p,176; htbl_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,112; xi_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,112; key_p,176; htbl_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 896; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
               byte_list_at ibytes in_p (word 112) s /\
               read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,11) s = rk /\
               htable_mem_8 (ghash_twist H) htbl_p s)
          (\s. read PC s = word (pc + 3756) /\
               read X9 s = word 112 /\
               byte_list_at (gcm_dec128_pt_bytes 112 ibytes ctr0 rk) out_p (word 112) s /\
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
  WB_READABLE_TAC 7 AES128_GCM_DEC_ALT_BUF_7BLOCK);;

let AES128_GCM_DEC_ALT_8BLOCK = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 128 /\ LENGTH rk = 11 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,128; xi_p,16; ivec_p,16]
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,128; key_p,176; htbl_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,128; xi_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,128; key_p,176; htbl_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 1024; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
               byte_list_at ibytes in_p (word 128) s /\
               read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,11) s = rk /\
               htable_mem_8 (ghash_twist H) htbl_p s)
          (\s. read PC s = word (pc + 3756) /\
               read X9 s = word 128 /\
               byte_list_at (gcm_dec128_pt_bytes 128 ibytes ctr0 rk) out_p (word 128) s /\
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
  WB_READABLE_TAC 8 AES128_GCM_DEC_ALT_BUF_8BLOCK);;

(* ---- the <=8-block dispatch theorem ----------------------------------------
   ONE readable theorem for every whole-blocks call with 1 <= nblk <= 8:
   symbolic nblk, bit_len C-argument = word (128*nblk), byte_list_at in/out
   over the whole 16*nblk-byte buffer, same NIST vocabulary as the bands.
   Proof: 8-way case split on nblk, each case reduces 16*k/128*k to numerals
   and MATCH_MP_TACs the band theorem. *)
let AES128_GCM_DEC_ALT_DISPATCH = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p
    nblk ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     1 <= nblk /\ nblk <= 8 /\
     LENGTH ibytes = 16 * nblk /\ LENGTH rk = 11 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,16 * nblk; xi_p,16; ivec_p,16]
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,176; htbl_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,176; htbl_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
               read PC s = word (pc + 0x1c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word (128 * nblk); out_p; xi_p; ivec_p; key_p; htbl_p] s /\
               byte_list_at ibytes in_p (word (16 * nblk)) s /\
               read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,11) s = rk /\
               htable_mem_8 (ghash_twist H) htbl_p s)
          (\s. read PC s = word (pc + 3756) /\
               read X9 s = word (16 * nblk) /\
               byte_list_at (gcm_dec128_pt_bytes (16 * nblk) ibytes ctr0 rk) out_p (word (16 * nblk)) s /\
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

(* ========================================================================= *)
(* The export layer (no simulation).                                         *)
(*                                                                           *)
(* DISPATCH above states the input and output as whole-buffer byte lists     *)
(* over the key words as they sit in memory, an opaque initial counter       *)
(* block ctr0 and a free GHASH key H; call a theorem of that shape a spine.  *)
(* The exported theorems state the input and output per block, over the      *)
(* FIPS-197 key schedule, the NIST nonce||counter block and H = E_K(0^128).  *)
(* The lemmas below make that restatement for a symbolic block count, and    *)
(* WBN_EXPORT_FROM_SPINE_TAC (at the end of the section) applies it to a     *)
(* spine.                                                                    *)
(* ========================================================================= *)

(* EL of gcm_dec_blocks_from at a symbolic index (analogue of build_aes_ctr_el).*)
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

(* gcm_dec128_pt_bytes at symbolic nblk: (16 * nblk) DIV 16 = nblk whole     *)
(* blocks.                                                                   *)
let GCM_DEC128_PT_BYTES_WHOLE_SYM = prove
 (`!nblk ibytes ctr0 rk. 1 <= nblk
     ==> gcm_dec128_pt_bytes (16 * nblk) ibytes ctr0 rk =
         aes128_ctr_bytes ctr0 (gcm_dec_blocks_from 0 nblk ibytes) rk`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gcm_dec128_pt_bytes] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* POINTWISE data-output support.                                            *)
(*                                                                           *)
(* WHY these exist: the spine's data postcondition is the whole-buffer       *)
(* byte-list form byte_list_at(gcm_dec128_pt_bytes(16*nblk)..), which reads  *)
(* as though arbitrary byte lengths were accepted.  The pointwise form       *)
(*   !j. j<nblk ==> read(memory:>bytes128(out_p+16j)) s =                    *)
(*                  EL j (aes128_ctr ...)                                    *)
(* says the routine handles whole blocks and matches the sibling AES-GCM     *)
(* proofs' shape, which the exported theorems use.  Do NOT "simplify" it     *)
(* away by folding it back into the byte-list form.                          *)

(* 16 bytes at offset 16*j of int128_list_to_bytes repack to EL j.  The reverse
   direction of the int128-list/byte-list correspondence; no such lemma existed.
   By induction on cts and cases on j: block 0 is the first 16 bytes
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

(* byte_list_at(gcm_dec128_pt_bytes ...) -> the per-block bytes128 reads.  At
   16 * nblk bytes gcm_dec128_pt_bytes is the flattened counter-mode stream
   over the nblk input blocks (GCM_DEC128_PT_BYTES_WHOLE_SYM), so each 16-byte
   slice is exactly EL j of it: BYTE_LIST_AT_1BLOCKS at byte 16 * j reads
   block j as that slice, and the repack lemma above closes it back to EL j. *)
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
(* Counter-model bridge to the NIST SP 800-38D nonce||counter form used by the *)
(* sibling AES-GCM proofs, wired into the exported theorems' nonce-named        *)
(* keystream.                                                                  *)
(*                                                                             *)
(* Our chain names counters via gcm_ctr_inc_iter j ctr0 (successor-iterated     *)
(* over an OPAQUE initial block ctr0).  The sibling proofs instead use          *)
(*   ctr_block nonce ctr = word_join (nonce:96 word) (word ctr:int32)          *)
(* (NIST big-endian: fixed 96-bit nonce, 32-bit big-endian counter).  These     *)
(* lemmas prove the two models COINCIDE: gcm_ctr_inc_iter is exactly NIST inc32 *)
(* iterated on the nonce||counter block (conjugated by the load-time byteswap), *)
(* UNCONDITIONALLY (the 32-bit wrap is the intended mod-2^32 rollover).          *)
(* GCM_CTR_INC_ITER_CTR_BLOCK is what lets the exported _CORRECT and         *)
(* _SUBROUTINE_CORRECT name the nonce (via WBN_OUTPUT_POINTWISE_NONCE and    *)
(* GCM_CTR_INC_ITER_NIST_IVEC below).  ctr_block is the shared NIST counter  *)
(* block of arm/proofs/utils/aes_gcm_spec.ml (loaded first, through          *)
(* aes_gcm_common.ml).                                                       *)
(* ------------------------------------------------------------------------- *)

(* NIST inc32 on a nonce||counter block just increments the 32-bit counter --    *)
(* UNCONDITIONALLY (word (c+1):int32 = word_add (word c) (word 1), the wrap is    *)
(* the intended mod-2^32 counter rollover).                                      *)
let INC32_CTR_BLOCK = prove
 (`!(nonce:96 word) c. inc32 (ctr_block nonce c) = ctr_block nonce (c + 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[inc32; ctr_block] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_BLAST
    `word_subword (word_join (nonce:96 word) (wc:int32):int128) (0,32):32 word = wc`;
              WORD_BLAST
    `word_subword (word_join (nonce:96 word) (wc:int32):int128) (32,96):96 word = nonce`] THEN
  REWRITE_TAC[WORD_ADD] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(* ... iterated: j applications of inc32 advance the counter by j.               *)
let ITER_INC32_CTR_BLOCK = prove
 (`!j (nonce:96 word) c. ITER j inc32 (ctr_block nonce c) = ctr_block nonce (c + j)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[ITER; ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[INC32_CTR_BLOCK] THEN REWRITE_TAC[INC32_CTR_BLOCK] THEN
  AP_TERM_TAC THEN ARITH_TAC);;

(* THE BRIDGE: our gcm_ctr_inc_iter j ctr0 equals the NIST nonce||counter block  *)
(* advanced by j, provided the byteswapped ctr0 decomposes as nonce||c.  Via     *)
(* GCM_CTR_INC_ITER_INC32 (gcm_ctr_inc_iter = bytereverse . ITER inc32 .          *)
(* bytereverse, in the layer above).                                             *)
let GCM_CTR_INC_ITER_CTR_BLOCK = prove
 (`!j (nonce:96 word) c ctr0.
     word_bytereverse ctr0 = ctr_block nonce c
     ==> gcm_ctr_inc_iter j ctr0 = word_bytereverse (ctr_block nonce (c + j))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GCM_CTR_INC_ITER_INC32] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[ITER_INC32_CTR_BLOCK]);;

(* ------------------------------------------------------------------------- *)
(* Bridge: the whole-buffer byte-list output collapses to the per-block,     *)
(* NIST-nonce-named keystream form of the exported theorems.                 *)
(* byte_list_at(gcm_dec128_pt_bytes ..) -> !j<nblk. read bytes128(out+16j)   *)
(* = pt_j XOR E_K(nonce||(c+j)), given word_bytereverse ctr0 = ctr_block     *)
(* nonce c.  Combines WBN_OUTPUT_POINTWISE (byte_list -> EL j of             *)
(* aes128_ctr), EL_AES128_CTR (element = pt XOR E_K(counter)) and            *)
(* GCM_CTR_INC_ITER_CTR_BLOCK (our gcm_ctr_inc_iter counter = the            *)
(* byte-reversed NIST nonce||(c+j) block).                                   *)
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
(* ABSTRACT INDEXED-INPUT bridges: re-present the exported                     *)
(* contracts over an ABSTRACT input function `inblock : num -> int128` pinned   *)
(* by a per-block read hypothesis, matching the sibling AES-GCM proofs'         *)
(* shape (input abstract, pinned by hypothesis).  The internal byte-list spine  *)
(* is instantiated with the concrete witness                                    *)
(*   ibytes := int128_list_to_bytes (list_of_seq inblock nblk)                  *)
(* and these lemmas discharge the spine's byte_list_at precondition and rewrite *)
(* its EL/nist_input_block_bytes byte-list vocabulary back to `inblock`.        *)
(* Sim-free.                                                                    *)
(* ------------------------------------------------------------------------- *)

(* pointwise list_of_seq congruence (only the values at i < n matter), by
   LIST_EQ as lists.ml proves LIST_OF_SEQ_EQ_SELF. *)
let LIST_OF_SEQ_EQ_PTWISE = prove
 (`!(f:num->B) g n. (!i. i < n ==> f i = g i) ==> list_of_seq f n = list_of_seq g n`,
  SIMP_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ]);;

(* INPUT ASSEMBLER: the per-block int128 reads (= inblock j) assemble into the  *)
(* byte_list_at precondition the spine expects, at ibytes = the flattened list. *)
(* The mirror of WBN_OUTPUT_POINTWISE (byte_list_at -> per-block reads); here    *)
(* per-block reads -> byte_list_at.  Byte i of the flattened list and the byte  *)
(* at in_p + i are both byte i MOD 16 of block i DIV 16                         *)
(* (EL_INT128_LIST_TO_BYTES, BYTE8_OF_BYTES128).                                *)
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

(* identity A: input block j read off the assembled ibytes IS inblock j.        *)
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

(* identity A': gcm_dec_blocks_from over the assembled ibytes IS inblock.       *)
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

(* identity B: the GHASH input list over the assembled ibytes IS the shared  *)
(* NIST (big-endian) view of inblock.  For decrypt, GHASH runs over the      *)
(* ciphertext, which is the input, so the spines' byte-list view             *)
(* nist_input_block_bytes becomes nist_input_block (aes_gcm_spec.ml).        *)
let NIST_INPUT_OF_ASSEMBLED = prove
 (`!inblock nblk.
     list_of_seq
       (nist_input_block_bytes (int128_list_to_bytes (list_of_seq inblock nblk))) nblk =
     list_of_seq (nist_input_block inblock) nblk`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC LIST_OF_SEQ_EQ_PTWISE THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[nist_input_block_bytes; nist_input_block] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC INBLOCK_OF_ASSEMBLED THEN ASM_REWRITE_TAC[]);;

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
(* Scalar rung lemmas for nblk > 8 (generalizations of the <=8-block         *)
(* scalar rungs).  All pure word/arith, no sim.                              *)
(*                                                                           *)
(* NOTE (signed pointer compares): the cmp x0,x5 at 0x33c/0x3a8/0x7d4 feed   *)
(* b.ge/b.lt = SIGNED conditions on pointers.  For nblk <= 8 x5 = in_p so    *)
(* the compare was reflexive; for nblk > 8 the exactness of                  *)
(* ival(x0) - ival(x5) needs the buffer to not straddle the 2^63 signed     *)
(* boundary: the premise val in_p + 16 * nblk < 2 EXP 63 (satisfied by all  *)
(* userspace buffers).                                                       *)
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

(* d = 128*((nblk-1) DIV 8) > 128 iff nblk >= 17 (drives the 0x3b0 skip) *)
let D_GT_128 = prove
 (`!nblk. 17 <= nblk ==> (128 < 128 * (nblk - 1) DIV 8 <=> T)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(ARITH_RULE `2 <= q ==> 128 < 128 * q`) THEN
  SUBGOAL_THEN `16 <= nblk - 1` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN ASM_ARITH_TAC);;

(* gcm_ctr_raw_def is defined above wb_front_postcond, whose ivec conjunct
   `read Q30 s = gcm_ctr_raw (word 8) ctr0` references it; its lane lemmas
   SUBW_RAW_* and GCM_CTR_RAW_INCR sit with the tail machinery. *)

(* ivec: the raw counter accumulator ABSORBS a prior gcm_ctr_add
   into its own offset.  gcm_ctr_raw v (gcm_ctr_add u x) = gcm_ctr_raw (word_add u v) x.
   Needed by INNER_TAIL_FEED_TAC to discharge the SHIFTED tail's Q30 (the shift sets
   ctr0 := gcm_ctr_add (word 8*(q+1)) ctr0) against the EXT2 seam's Q30, and by the
   FULL_r ivec reconcile.  Proved at 32-bit-LANE granularity so the symbolic 32-bit
   addend never enters a 128-bit BDD (a naive WORD_BLAST HANGS).
   gcm_ctr_raw reads only the 4 lanes of its arg; gcm_ctr_add rewrites only lane
   (96,32); so the low 3 lanes pass through and the top lane composes the two adds. *)
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

(* 32-bit-lane insert passthrough: the low 3 lanes are unaffected by the top insert. *)
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
(* The >=9 front: the entry pc+0x1c to the loop head 0x3b4 (pc+948).         *)
(*                                                                           *)
(* Against the 5..8 leg WB_FRONT_BUF:                                        *)
(*  - the band 5 <= nblk /\ nblk <= 8 becomes 17 <= nblk /\                  *)
(*    128 * nblk < 2 EXP 64 /\ val in_p + 16 * nblk < 2 EXP 63 (the signed  *)
(*    pointer compares must not straddle 2^63);                              *)
(*  - after the shared WBN_FRONT_PREBRANCH (steps 1..201) the 0x340 b.ge     *)
(*    falls through (WB_LOOPENTER_FLAGS_GE9), the front-N 0x344..0x3ac       *)
(*    (steps 203..229) loads input blocks 0..7, stores plaintext blocks      *)
(*    0..7 and advances the counter chain to 13, and the 0x3b0 b.ge (step    *)
(*    230) falls through to the loop head (WB_PTRCMP_FLAGS, D_GT_128).       *)
(* ------------------------------------------------------------------------- *)

(* The >=17 front hypotheses: wb_front_hyps_tm with its 5 <= nblk /\        *)
(* nblk <= 8 prefix replaced by the >=17 band, keeping every other           *)
(* conjunct, plus two out_p disjointness facts the <=8 hypotheses do not     *)
(* need.  The front-N stores to out_p (stp q0,q1,[x2],#32 at 0x350, step     *)
(* 204, and three more) before the loop head: without out_p against the      *)
(* stack the stores would drop the reduction constant at [sp+64], and        *)
(* without out_p against in_p the first store, which comes before the        *)
(* ldp's of input blocks 2..7 (steps 207, 208, 211), would drop every input  *)
(* fact, so those loads would read unknown values.                           *)
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

(* pure-arith closer for the nblk >= 17 side conditions *)
let NBLK_ARITH_TAC =
  MP_TAC(ASSUME `17 <= nblk`) THEN MP_TAC(ASSUME `128 * nblk < 2 EXP 64`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;;

(* The 0x3b0 b.ge (step 230): after the cmp x0,x5 at 0x3a8 X0 = in_p + 128  *)
(* and X5 = in_p + d with d = 128 * ((nblk - 1) DIV 8) > 128 for            *)
(* nblk >= 17, so NF is true and VF false: it falls through to the loop     *)
(* head 0x3b4.                                                               *)
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
(* The front prefix, simulated once.  The >=17 band (WBN_FRONT_BUF, to the   *)
(* loop head) and the 9..16 band (to the prepretail 0x7fc) run the same      *)
(* steps up to the 0x3b0 b.ge and differ only there, so the prefix (entry    *)
(* to 0x3b0) is proved once on the union band 9 <= nblk (WBN_FRONT_PREFIX),  *)
(* keeping the NZCV facts of the cmp x0,x5 at 0x3a8 that the b.ge reads.     *)
(* Each band then resolves the branch in a one-step leg chained by           *)
(* ENSURES_TRANS_SIMPLE.                                                     *)
(* ------------------------------------------------------------------------- *)

(* the union band: wbn_front_hyps_tm with 17 <= nblk relaxed to 9 <= nblk *)
let wbn_front_hyps_ge9_tm =
  let rec repl t = match t with
    | Comb(Comb(Const("/\\",_),a),b) -> mk_conj(repl a, repl b)
    | _ -> if t = `17 <= nblk` then `9 <= nblk` else t in
  repl wbn_front_hyps_tm;;

(* The 0x340 b.ge falls through whenever d = 128 * ((nblk - 1) DIV 8) >= 1, *)
(* i.e. nblk >= 9: the cmp x0,x5 at 0x33c compares in_p with in_p + d,      *)
(* the a = 0 case of WB_PTRCMP_FLAGS.                                       *)
let WB_LOOPENTER_FLAGS_GE9 = prove
 (`!(in_p:int64) nblk. 9 <= nblk /\ 128 * nblk < 2 EXP 64 /\
        val in_p + 16 * nblk < 2 EXP 63
    ==> (ival (word_sub in_p (word_add (word (128 * (nblk - 1) DIV 8)) in_p)) < &0 <=> T) /\
        (ival in_p - ival (word_add (word (128 * (nblk - 1) DIV 8)) in_p) =
         ival (word_sub in_p (word_add (word (128 * (nblk - 1) DIV 8)) in_p)) <=> T)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`in_p:int64`; `0`; `128 * (nblk - 1) DIV 8`] WB_PTRCMP_FLAGS) THEN
  REWRITE_TAC[WORD_ADD_0] THEN ARITH_TAC);;

(* pure-arith closer for the union-band side conditions *)
let NBLK_ARITH_GE9_TAC =
  MP_TAC(ASSUME `9 <= nblk`) THEN
  MP_TAC(ASSUME `128 * nblk < 2 EXP 64`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;;

(* the 0x340 b.ge falls through, by WB_LOOPENTER_FLAGS_GE9 *)
let WBN_RESOLVE_324_GE9_TAC : tactic =
  MP_TAC(SPECL [`in_p:int64`; `nblk:num`] WB_LOOPENTER_FLAGS_GE9) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]));;

(* prefix goal builder (union band, postcondition at the 0x3b0 b.ge) *)
let mk_wbn_prefix_goal postcond =
  let ens = subst [wb_front_pre_tm,`PPP:armstate->bool`; postcond,`QQQ:armstate->bool`;
                   wb_front_frame_tm,`CCC:armstate->armstate->bool`]
              `ensures arm PPP QQQ CCC` in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_ge9_tm, ens));;

(* The s229 prefix postcondition, the state at the 0x3b0 b.ge: input blocks *)
(* 0..7 in Q8..Q15, plaintext blocks 0..7 stored and 5..7 still in Q5..Q7,   *)
(* the counters 8..12 in Q0..Q4 and Q30 = the raw counter + 13, with the     *)
(* NZCV facts of the cmp x0,x5 at 0x3a8.  The key, htable, tag and ivec      *)
(* memory facts do not survive the first out_p store (step 204), and the    *)
(* input-buffer facts are not restated; the extended layer below re-adds    *)
(* the input buffer, the keys and the htable, which the frame preserves.     *)
(* Built like wb_front_postcond, as the final state of the prefix            *)
(* simulation.                                                               *)
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
   `read X3 s = xi_p`;
   `read X6 s = htbl_p`] @
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

(* Input blocks 0..7 as 128-bit lanes at s201, for the ldp q8..q15 of the    *)
(* front-N, from the input-buffer fact; the SPECL state must be the one      *)
(* ENSURES_INIT_TAC names in WBN_FRONT_PREFIX.                               *)
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

(* THE FRONT PREFIX (union band 9 <= nblk): WBN_FRONT_PREBRANCH (steps       *)
(* 1..201), then the 0x340 b.ge falls through (step 202) and the front-N     *)
(* runs steps 203..229 to the 0x3b0 b.ge (pc+944).  The ABI frame is         *)
(* unfolded before the simulation, so the final state discharges it.         *)
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

(* The s230 postcondition at the loop head, the i = 0 instance of the loop   *)
(* invariant below: the facts of wbn_front_prefix_postcond one step later,   *)
(* after the 0x3b0 b.ge, in reverse order, with PC = pc+948 and without the  *)
(* NF and VF facts.                                                          *)
let wbn_front_postcond_i0 =
  let cs = conjuncts(snd(dest_abs wbn_front_prefix_postcond)) in
  let nf_vf c = try mem (rand(rator(lhs c))) [`NF`; `VF`] with Failure _ -> false in
  wbp_post (hd cs :: `read PC s = word (pc + 948)` ::
            filter (not o nf_vf) (rev (tl (tl cs))));;

(* THE >=17 FRONT: WBN_FRONT_PREFIX, then the 0x3b0 b.ge (step 230) falls    *)
(* through to the loop head 0x3b4 = pc+948 (WBN_RESOLVE_394_TAC).            *)
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
(* WBN_FRONT_BUF's postcondition generalized to the iteration index i:      *)
(*  - the store/counter stream runs ahead at 8(i+1): X0 = in_p + 128(i+1),   *)
(*    X2 = out_p + 128(i+1), Q0..Q4 = the counters 8i+8..8i+12, Q5..Q7 =    *)
(*    the plaintexts of blocks 8i+5..8i+7 (already stored), the stores      *)
(*    done for all j < 8(i+1), Q30 = the raw counter + 8i+13;               *)
(*  - the GHASH stream lags at 8i: Q19 = the accumulator over the raw       *)
(*    ciphertext blocks 0..8i-1, Q8..Q15 = the raw blocks 8i..8i+7 not yet  *)
(*    folded in.                                                             *)
(* The loop body and the prepretail read exactly these registers (Q0..Q4,    *)
(* Q8..Q15, Q19, Q30, Q31, X0, X2, X4, X5, X6, X10, X11); the round keys    *)
(* the front leaves in Q26, Q27 and Q28 are dead (both reload them before    *)
(* use), and the remaining conjuncts are facts the later legs pass through.  *)
(* The loop control is the cmp x0,x5 at 0x7d4 and the signed b.lt 0x3b4 at   *)
(* 0x7f8; the exit falls through to the prepretail 0x7fc (pc+2044); the     *)
(* loop runs (nblk - 9) DIV 8 times.                                         *)
(* ------------------------------------------------------------------------- *)

let wbn128_loop_invariant = new_definition
 `wbn128_loop_invariant (pc:num) (ctr0:int128) (in_p:int64) (out_p:int64)
    (xi_p:int64) (ivec_p:int64) (key_p:int64) (htbl_p:int64) (stackpointer:int64)
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
    htable_mem_dec h htbl_p s`;;

(* ------------------------------------------------------------------------- *)
(* Strengthening an ensures postcondition with a fact the frame preserves,  *)
(* with no re-simulation: from `ensures step P Q C` and                      *)
(* `!s s'. P s /\ C s s' ==> R s'`, `ensures step P (\s. Q s /\ R s) C`.     *)
(* ENSURES_SUBLEMMA_THM with the same precondition and frame.                *)
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
(* head, which the simulated postcondition drops (the key and htable facts   *)
(* do not survive the first out_p store) but the front frame preserves: it   *)
(* writes only out_p, xi_p, ivec_p, [sp+64..80) and registers.  The          *)
(* preservation needs out_p disjoint from key_p and htbl_p as well, which    *)
(* the wide hypotheses add (out_p against in_p is already in                 *)
(* wbn_front_hyps_tm).                                                       *)
(* ------------------------------------------------------------------------- *)

(* the wide >=17 hypotheses: wbn_front_hyps_tm + out_p vs key_p and htbl_p *)
let wbn_front_hyps_wide_tm =
  mk_conj(wbn_front_hyps_tm,
    `nonoverlapping (out_p:int64,16 * nblk) (key_p:int64,176) /\
     nonoverlapping (out_p:int64,16 * nblk) (htbl_p:int64,192)`);;

(* the WBN_FRONT_BUF pieces: P = precondition, Q0 = simulated postcondition, *)
(* C = frame *)
let wbn_front_P_tm, wbn_front_Q0_tm, wbn_front_C_tm =
  let ens = snd(dest_imp(snd(strip_forall(concl WBN_FRONT_BUF)))) in
  rand(rator(rator ens)), rand(rator ens), rand ens;;

(* R = the loop constants, as the invariant states them *)
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
     `htable_mem_dec h (htbl_p:int64) s`]);;

(* push a read through the frame's write chain to `read c s` with the        *)
(* nonoverlapping assumptions, then close it by the precondition fact        *)
let WBN_PUSH_LHS_READ_TAC : tactic =
  W(fun (asl,w) ->
    let thl = map snd asl in
    let cxt = (NONOVERLAPPING_DRIVERS thl, FILTER_CANONIZE_ASSUMPTIONS thl) in
    CONV_TAC(LAND_CONV(COMPONENTS_READ_OVER_WRITE_ORTHOGONAL_CONV cxt))) THEN
  ASM_REWRITE_TAC[];;

(* The prefix with the loop constants, on the wide union band, for both      *)
(* legs from the 0x3b0 b.ge: the >=17 loop entry and the 9..16 leg to the    *)
(* prepretail.                                                               *)
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
    [`pc:num`;`ctr0:int128`;`in_p:int64`;`out_p:int64`;`xi_p:int64`;`ivec_p:int64`;
     `key_p:int64`;`htbl_p:int64`;`stackpointer:int64`;`nblk:num`;`ibytes:byte list`;
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
    [`pc:num`;`ctr0:int128`;`in_p:int64`;`out_p:int64`;`xi_p:int64`;`ivec_p:int64`;
     `key_p:int64`;`htbl_p:int64`;`stackpointer:int64`;`nblk:num`;`ibytes:byte list`;
     `xi:int128`;`h:int128`;`k0:int128`;`k1:int128`;`k2:int128`;`k3:int128`;`k4:int128`;
     `k5:int128`;`k6:int128`;`k7:int128`;`k8:int128`;`k9:int128`;`k10:int128`]);;

let wbn_core_iv = list_mk_abs([`i:num`;`s:armstate`],
  mk_comb(mk_comb(wbn_core_applied,`i:num`),`s:armstate`));;

(* The loop: PC = pc+948 /\ core 0 ==> PC = pc+2044 /\ core k, over the      *)
(* front frame (WBN_MAIN_LOOP_raw in the AES-256 proof), and one iteration   *)
(* of its body: PC = pc+948 /\ core i ==> PC = (if i + 1 < k then pc+948     *)
(* else pc+2044) /\ core (i+1), for every i < k.                             *)
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

(* ------------------------------------------------------------------------- *)
(* GHASH 8-block extension algebra (no simulation).                          *)
(*                                                                           *)
(* The invariant's Q19 is the byte-reversed GHASH fold over the raw          *)
(* ciphertext blocks 0..8i-1.  The loop body and the prepretail each fold    *)
(* one more 8-block group (8i..8i+7), so the fold over 8(i+1) blocks must    *)
(* equal the fold over 8i blocks continued by the 8 Horner steps, in the     *)
(* machine's 8-block byteform (GHASH_ACC_APPEND, list_of_seq).               *)
(* ------------------------------------------------------------------------- *)

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

(* The main lemma: extend the invariant's GHASH fold by one 8-block          *)
(* group.  RHS = the 8*i fold, continued by a fold over the 8 concrete new    *)
(* raw-ct blocks (8*i .. 8*i+7).  Instantiate blk := \k. bytes_to_int128      *)
(* (SUB_LIST (16*k,16) ibytes) in the body; REWRITE_TAC[MAP; ghash_polyval_acc]*)
(* then unfolds the RHS to the nested polyval_dot/word_xor Horner chain the   *)
(* 8 body GHASH instructions produce. *)
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

(* Body GHASH-close bridge: the generalization of the <=8 chain's             *)
(* spec_to_byteform_wb8 to an ARBITRARY incoming accumulator `acc` (the running *)
(* fold read Q19 at body entry) in place of the tail's hardwired              *)
(* `word_bytereverse xi`.  Same H-power hypotheses (supplied by the htable    *)
(* reduce steps during the sim), same machine byteform RHS.  Proof is verbatim  *)
(* the <=8 chain's (STRIP; GHASH_POLYVAL_ACC_8; ASM_REWRITE; AP_TERM;         *)
(* WORD_RULE) --                                                              *)
(* it never depended on the acc being xi.  Composes with GHASH_ACC_8BLOCK_EXTEND *)
(* (acc := the invariant's 8*i fold) to close the loop body's Q19.            *)
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

(* The COMPOSED body Q19-close: the invariant's Q19 conjunct at               *)
(* i+1 equals the machine 8-block byteform, with the incoming accumulator being  *)
(* the invariant's OWN 8*i fold.  = GHASH_ACC_8BLOCK_EXTEND (split the 8*(i+1)   *)
(* fold into [8 fresh blocks] on the 8*i fold) then SPEC_TO_BYTEFORM_WB8_ACC  *)
(* (acc := that 8*i fold).  This is exactly what the loop body's Q19 SUBGOAL  *)
(* must match once the store/GHASH window is simulated with the raw reduce    *)
(* preserved (H-power hyps `byteswap128 h2..h8 = polyval_dot..` are produced by  *)
(* the htable reduce steps during the sim).  Proved to hyps=0: the whole GHASH   *)
(* algebra of the body close is settled here, sim-free.                       *)
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
(* The GHASH reduce, as a value equality.                                    *)
(*                                                                           *)
(* The loop body (0x700..0x7c8) and the prepretail (0xb04..0xba0) wire       *)
(* the three Karatsuba accumulators PL = Q17, PH = Q19 and PM = Q18 into     *)
(* the shared reduction: eor3 v18,v18,v17,v19 (the Karatsuba tidy), pmull    *)
(* v29 and ext v21 of PL, eor3 v18,v18,v29,v21, pmull v17 and ext v21 of     *)
(* v18, and the final eor3 v19,v19,v17,v21.  The final fold's operand        *)
(* order is the AES-256 kernel's swapped (eor3 v19,v19,v21,v17 there), so    *)
(* the byteform LHS below is (PH ^ pmul) ^ ext rather than                   *)
(* (PH ^ ext) ^ pmul; the identity is the same.  It is derived from the      *)
(* shared POLYVAL_REDUCE_G2 (aes_gcm_common.ml): pack_corrected is           *)
(* karatsuba_join, so the RHS is polyval_reduce_g2 PL PH PM.  The            *)
(* statement keeps pack_corrected because KARA_ACC_PACK_HELPER, which packs  *)
(* the eight per-block triples in the Q19 close below, is stated with it.    *)
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
(* BLOCK-ALGEBRA reconciliation                                               *)
(* facts.  These bridge the machine's wire-in accumulators (Q17/Q19/Q18 = the *)
(* separable Sigma-PL/PH/PM triple, in raw word_reversefields/word_join/      *)
(* byteswap128-tower form) to the abstract kara_acc projection of an 8-quad   *)
(* list, so KARA_ACC_PACK_HELPER + KARATSUBA_BLOCK_PACKS_TO_PMUL_CLEAN can    *)
(* pack them to Sum_k word_pmul input_k h_k = BODY_Q19_CLOSE_ALGEBRA's prop3  *)
(* argument.  All are pure free-variable WORD_BLAST/WORD_RULE identities.     *)
(* --------------------------------------------------------------------------- *)

(* fact 1: the two byte-reversal spellings coincide (machine uses reversefields *)
(* 8, the spec/kara side uses word_bytereverse). *)
let WRF8_IS_BYTEREVERSE = prove
 (`!x:int128. word_reversefields 8 x = word_bytereverse x`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* fact 2: karatsuba_mid is byteswap-invariant (it XORs the two 64-halves, and *)
(* byteswap128 swaps them).  Lets the htable mid cell `karatsuba_mid h` satisfy *)
(* KARATSUBA_BLOCK_PACKS_TO_PMUL_CLEAN's `subword hk (0,64) = karatsuba_mid   *)
(* (byteswap128 h)` precondition. *)
let KMID_BYTESWAP_INV = prove
 (`!h:int128. karatsuba_mid h = karatsuba_mid (byteswap128 h)`,
  GEN_TAC THEN REWRITE_TAC[karatsuba_mid; byteswap128] THEN CONV_TAC WORD_BLAST);;

(* fact 3 (block-0 SOFAR lane-collapse): block 0's operand enters via a rot64'd *)
(* word_join of the running accumulator SOFAR with the first ciphertext block.  *)
(* The reduce takes the (64,64) / (0,64) sub-lane of the XOR of the two joins,  *)
(* which collapses to the plain (0,64) / (64,64) sub-lane of `word_xor S X`.  *)
let LANE_COLLAPSE = prove
 (`(!S X:int128. word_subword (word_xor (word_subword (word_join S S:256 word) (64,128):128 word)
                            (word_subword (word_join X X:256 word) (64,128):128 word)) (64,64):64 word
    = word_subword (word_xor S X) (0,64):64 word) /\
   (!S X:int128. word_subword (word_xor (word_subword (word_join S S:256 word) (64,128):128 word)
                            (word_subword (word_join X X:256 word) (64,128):128 word)) (0,64):64 word
    = word_subword (word_xor S X) (64,64):64 word)`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* fact 4 (pmull2/pmull PAIR mid-input lanes): the machine computes the PM mid  *)
(* products two blocks at a time (a pmull2 then pmull over the packed lanes of  *)
(* blocks A and B).  The (64,64)/(0,64) sub-lane of the XOR of the hi-join and  *)
(* lo-join recovers each single block's (lo XOR hi) mid-input. *)
(* The mid-input lane extractors used by the Q19 reduce.  Only the            *)
(* swapped-RHS PM_LANE_HI'/LO' variants below are consumed (by                *)
(* build_q19_reduce_clean and build_q19_reduce_clean_idx): they spell the     *)
(* extracted mid-input in the (0,64)^(64,64) lane order that karatsuba_block_pm *)
(* produces (word_pmul's first arg is atomic to WORD_RULE, so the lane XOR must *)
(* match SYNTACTICALLY, not up to comm).                                      *)
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

(* Block-0/block-1 SOFAR-pair PM mid-inputs.  The FIRST pmull2/               *)
(* pmull PAIR folds in the running accumulator SOFAR, so block 0's operand    *)
(* enters as a rot64'd word_join of SOFAR with the first ciphertext block     *)
(* (not the plain packed pair the later blocks use).  These two lane lemmas   *)
(* recover the block-0 (outer (64,64), over word_xor SOFAR cph0) and block-1  *)
(* (outer (0,64), over cph1) mid-inputs, in karatsuba_block_pm's (0,64)^(64,64) *)
(* lane order.  Pure WORD_BLAST over free ss (=SOFAR), xx0 (=rev cph0), xx1   *)
(* (=rev cph1).  Together with PM_LANE'_HI/LO (the plain pairs {2,3}{4,5}{6,7}) *)
(* they reduce all 8 machine PM mid-inputs to kara form so PROJ_EQ PM closes. *)
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

(* --------------------------------------------------------------------------- *)
(* Compose the value-equality into the Q19 close.                             *)
(*                                                                            *)
(* build_q19_reduce_clean pl_t ph_t pm_t : given the three accumulator terms  *)
(* at the wire-in state (read Q17/Q19/Q18, over h/xi/ibytes/i), produces the  *)
(* CLEAN theorem                                                              *)
(*   |- <machine reduce byteform> = ghash_polyval_acc (byteswap128 h)         *)
(*   (word_bytereverse xi) (MAP word_bytereverse (list_of_seq blk (8*(i+1)))) *)
(* hyps=0 -- the invariant's Q19-at-(i+1) fold.  It chains:                   *)
(*   reduce_id  : byteform = polyval_reduce_prop3 (pack_corrected PL PH PM)   *)
(*                                        [WBN_MACHINE_REDUCE_IS_PROP3_PACK]  *)
(*   KARA_PACK_EQ (kqok): pack_corrected PL PH PM = SPEC_TOWERS               *)
(*   body_ready2 : ghash..(8(i+1)) = polyval_reduce_prop3 SPEC_TOWERS         *)
(*                                        [BODY_Q19_CLOSE_ALGEBRA + involution]  *)
(* The 8 kqok side-conditions (subword hk_j (0,64) = karatsuba_mid ..) are    *)
(* discharged by choosing hk_j := word_join (word 0)(karatsuba_mid ..) so kqok  *)
(* holds unconditionally (KMID_BYTESWAP_INV) -- a hyps-free                   *)
(* lemma.  PROJ_PM is kept CONDITIONAL on kqok (hk free) then INST'd+MP'd -- the *)
(* bake-hk-upfront variant fails PROJ_PM (subword(join 0 kmid) not plain kmid). *)

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

(* Wire-in tactics.  The extract stashes pl/ph/pm at the wire-in state into   *)
(* refs, before the ABBREV that makes the reduce window small; the close (run *)
(* at the Q19 postcondition conjunct) rebuilds the CLEAN theorem from those   *)
(* refs and accepts it after mapping its concrete byteform LHS back to the    *)
(* goal's PL/PH/PM-abbreviated form and the 8*(i+1) = 8*i+8 index            *)
(* normalization the postcondition preparation applied.                       *)
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

(* ------------------------------------------------------------------------- *)
(* The k-indexed variant of build_q19_reduce_clean, for the                   *)
(* PREPRETAIL Q19 close (index k = (nblk-9)DIV8, not the loop-body i).  The   *)
(* only delta is INST'ing BODY_Q19_CLOSE_ALGEBRA with i := idx first, so its  *)
(* spec fold reads ghash..(8*(idx+1)); everything else (the reduce identity   *)
(* + block algebra) is index-free.  The body could call this with `i:num`.    *)
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

(* WBN_Q19_PREPRETAIL_CLOSE_TAC idx : closes BOTH prepretail GHASH conjuncts  *)
(* (run per-conjunct after ENSURES_FINAL + REPEAT CONJ_TAC, guarded on        *)
(* ghash_polyval_acc).  idx = the prepretail index (`k:num`).  The Q19 conjunct  *)
(* (read Q19 = ghash..(8*(k+1))) and the Q16 staging conjunct                 *)
(* (read Q16 = word_subword(word_join <caught_up> <caught_up>)(64,128)) both  *)
(* reduce, after ASM_REWRITE substitutes the machine byteform + the CLEAN     *)
(* value-equality folds it to ghash..(8*k+8), to the pure index identity      *)
(* 8*k+8 = 8*(k+1), closed by ARITH + REFL.                                   *)
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
(* Counter folds for the raw counter in v30.                                 *)
(*                                                                           *)
(* The loop body and the prepretail read Q30 = gcm_ctr_raw (word w) ctr0     *)
(* (the counter byte-grouped as rev32 reads it, w added to its top lane):    *)
(* rev32 vk,v30 gives the AES input block gcm_ctr_add (word w) ctr0, and     *)
(* add v30,v30,v31 advances w by one.  REV32_FOLD_TAC and                    *)
(* CTR_RAW_INCR_FOLD_TAC fold the stepper's lane towers back to those        *)
(* forms after each such step, so later steps never nest them.               *)
(* ------------------------------------------------------------------------- *)

let REV32_FOLD_TAC (qd:string) (sn:string) (wtm:term) : tactic =
  fun (asl,gl) ->
    let tower = tryfind (fun (_,th) -> match concl th with
      | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),st)),r)
          when string_of_term c = qd && (try fst(dest_var st)=sn with _ -> false) -> r
      | _ -> fail()) asl in
    (* generalize wtm -> a fresh w:32 word, prove the fold for symbolic w, then re-specialize *)
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

(* CTR_RAW_INCR_FOLD_TAC qd sn wtm: the increment counterpart of REV32_FOLD_TAC.
   After an `add v30,v30,v31` + GCM_SIMD_SIMPLIFY_TAC, the assumption
   `read Qd sn = <single-add tower over gcm_ctr_raw wtm ctr0>` (top lane
   word_add (word_subword (gcm_ctr_raw wtm ctr0)(96,32))(word 1), others +0) folds
   to `read Qd sn = gcm_ctr_raw (word_add wtm (word 1)) ctr0` via GCM_CTR_RAW_INCR
   instantiated at w:=wtm.  Fold ONCE PER add (before the next add re-nests the
   +1s) so only the single-+1 GCM_CTR_RAW_INCR LHS is ever matched.
   (MATCH_ACCEPT on the exact simplified single-add shape.) *)
let CTR_RAW_INCR_FOLD_TAC (qd:string) (sn:string) (wtm:term) : tactic =
  let incr_spec = INST [wtm,`w:32 word`] GCM_CTR_RAW_INCR in
  RULE_ASSUM_TAC(fun th ->
    match concl th with
    | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),st)),_)
        when string_of_term c = qd && (try fst(dest_var st)=sn with _ -> false) ->
        REWRITE_RULE[incr_spec] th
    | _ -> th);;

(* ------------------------------------------------------------------------- *)
(* Steppers for the loop body and the prepretail.                            *)
(*                                                                           *)
(* CTR_INCR_NORM_TAC folds an add v30 and normalizes the counter index;      *)
(* the KEEPDATA steppers keep the latest read of each of Q0..Q19 (the        *)
(* keystreams, the raw ciphertext and the GHASH accumulators), all memory    *)
(* facts and the loop constants, and discard every other old-state fact;     *)
(* the NOSIMP variant is for the reduce and store windows.                   *)
(* ------------------------------------------------------------------------- *)

(* fold add-v30 increment then normalize the counter to word(8*i+(c+1)) *)
let CTR_INCR_NORM_TAC (sn:string) (c:int) : tactic =
  let cur = mk_comb(`word:num->32 word`,
    mk_binop `(+):num->num->num` `8*i` (mk_small_numeral c)) in
  let nrm = WORD_RULE (mk_eq(
    mk_binop `word_add:32 word->32 word->32 word` cur `word 1:32 word`,
    mk_comb(`word:num->32 word`,
      mk_binop `(+):num->num->num` `8*i` (mk_small_numeral (c+1))))) in
  CTR_RAW_INCR_FOLD_TAC "Q30" sn cur THEN RULE_ASSUM_TAC(REWRITE_RULE[nrm]);;

(* discard all-but-latest read Q19 s_ facts (the GHASH accumulator grows a big
   partial tower each step; older states are dead).  Mirror of the <=8 chain's
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

(* ---- body-close reduce-window infrastructure --------
   The final GHASH reduce (loop 0x700..0x7c8, prepretail 0xb04..0xba0) loads
   Q16 = the [sp+64] modulus (carried by the invariant) and feeds the
   pmull/eor3 chain via Q16/Q17/Q21/Q29.
   DISCARD_STALE_QREG_TAC qn keeps only the LATEST read of register qn (the
   generalization of DISCARD_STALE_Q19_TAC used by the KEEPDATA steppers). *)
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
(* nblk >= 9 from a loop index *)
let WBN_NBLK_GE_9 = prove
 (`i < (nblk - 9) DIV 8 ==> 9 <= nblk`,
  MP_TAC(SPECL [`nblk - 9`; `8`] DIVISION) THEN ARITH_TAC);;

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
(* The per-step fold here uses ONE pass of GCM_SIMD_SIMPLIFY_CORE_TAC, not
   the shared double-pass GCM_SIMD_SIMPLIFY_TAC.  The second pass exists (in the
   lemmas file) to reach a REV64 fixpoint that a single pass can miss on a few
   steps -- but under KEEPDATA (which discards stale old-state reads after every
   step) the body sim reaches its self-contained cut-points without that extra
   fold: the loop body and the prepretail (the only two KEEPDATA-SIMP
   users) both close with a single core pass.  KEEPGH (tails/fronts) and every
   other consumer keep the double-pass GCM_SIMD_SIMPLIFY_TAC.
   The pass is also Q-scoped and fixpoint-memoized, as gcm_simd_fixpt_tbl and
   gcm_simd_kgh_tbl are for the other steppers: its rules (REV64 lanes /
   WORD_SWAP_HALVES / EXT8_LANE0 / REV32_LANE_SUBWORD) can ONLY fire on a
   `read Qn s = <tower>` assumption, so the O(1) `read Qn` head is guarded
   before the rewrites, and a Q-read whose concl is a known F-fixpoint (table
   gcm_simd_kd_tbl) is skipped.  apply_F = the SAME 3 passes as
   GCM_SIMD_SIMPLIFY_CORE_TAC, so this is BIT-IDENTICAL by construction.  The
   cache is reset per simulation via CLEAR_KEEPDATA_MEMO_TAC (after each
   ENSURES_INIT in the 2 consumers) so each `prove` is hermetic. *)
let gcm_simd_kd_tbl : (term,unit) Hashtbl.t = Hashtbl.create 8192;;
let CLEAR_KEEPDATA_MEMO_TAC : tactic =
  fun (asl,w) -> Hashtbl.clear gcm_simd_kd_tbl; ALL_TAC (asl,w);;
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
(* NO-SIMPLIFY variant for the reduce + store windows: GCM_SIMD_SIMPLIFY on the
   concrete [sp+64] modulus pmull (reduce) or the kept eor3 keystream towers
   (store) explodes; step symbolic instead. *)
let ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC exec snums =
  MAP_EVERY (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN
              DISCARD_STALE_DATA_TAC THEN DISCARD_OLDSTATE_KEEPDATA_TAC s THEN CLARIFY_TAC)
    (statenames "s" snums);;

(* ------------------------------------------------------------------------- *)
(* The prepretail: from the loop exit 0x7fc (pc+2044) to the tail seam      *)
(* pc+3032.                                                                  *)
(*                                                                           *)
(* The loop exits at k = (nblk - 9) DIV 8 with the GHASH stream one 8-block *)
(* group behind.  The prepretail 0x7fc..0xbc0 (242 steps) folds that last   *)
(* in-flight group (blocks 8k..8k+7) into Q19 and computes the keystream     *)
(* towers of blocks 8k+8..8k+15 in Q0..Q7; the tail entry 0xbc4..0xbd4 (5    *)
(* steps: mov v29,v27; sub x5,x4,x0; cmp x5,#0x70; ldp q24,q25,[x6,#160];   *)
(* ldr q9,[x0],#16) then sets up the tail's registers.  The end state is    *)
(* the <=8 seam (wb_front_postcond) under the substitution                   *)
(*   ctr0  := gcm_ctr_add (word (8 * (k + 1))) ctr0,                        *)
(*   in_p  := in_p + 128 * (k + 1),  out_p := out_p + 128 * (k + 1),        *)
(*   nblk  := nblk - 8 * (k + 1)  (1..8),                                    *)
(*   xi    := the accumulator over all 8 * (k + 1) blocks,                   *)
(*   ibytes := the last nblk - 8 * (k + 1) blocks,                           *)
(* which the next layer uses to run the shared tail back-legs.               *)
(* Cut points: the counter folds at s5, s11, s19, s20, s36 and s235; the     *)
(* GHASH wire-in at s182, where PL, PH and PM are complete (their last       *)
(* writes are s182, s175 and s174), after which the reduce s195..s234 runs   *)
(* on the abbreviated accumulators; and the incoming Q9 (the first tail      *)
(* block) resolved at s246, before the ldr q9 at s247.                       *)
(* ------------------------------------------------------------------------- *)

(* The s247 seam state, built like wb_front_postcond, with Q19 stated at a   *)
(* fresh xi' as the substitution source for wbn_prepretail_post below (as   *)
(* written, with xi' unconstrained, it is not a true postcondition).  It     *)
(* drops what the tail does not read: the xi_p, ivec_p, [sp+72] and in_p     *)
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
    `read X3 s = xi_p`;
    `read X6 s = htbl_p`;
    `read (memory :> bytes (in_p,16 * nblk)) s = num_of_bytelist ibytes`] @
   wbp_key_reads @ wbp_htable_reads @ wbp_ctx `xi':int128` @
   [mk_eq(`read X5 s`, x5v);
    `read X0 s = word_add (word_add in_p (word (128 * ((nblk - 9) DIV 8 + 1)))) (word 16)`;
    `read Q29 s = k10`]);;

(* The caught-up GHASH accumulator: the invariant's Q19 at i := k + 1, the  *)
(* fold over all 8 * (k + 1) processed blocks.                               *)
let wbn_caught_up = `ghash_polyval_acc (byteswap128 (h:int128)) (word_bytereverse (xi:int128))
    (MAP word_bytereverse
    (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) (ibytes:byte list)))
                 (8 * (((nblk:num) - 9) DIV 8 + 1))))`;;

(* the seam post with Q19 = the caught-up accumulator (xi' gone) *)
let wbn_prepretail_post =
  subst [wbn_caught_up, `word_bytereverse (xi':int128)`] wbn_prepretail_post_raw;;

(* the first tail block's index is in range: 8 * k + 8 < nblk *)
let WBN_Q9_INDEX_LT_9 = prove
 (`!nblk. 9 <= nblk /\ 128 * nblk < 2 EXP 64 ==> 8 * ((nblk - 9) DIV 8) + 8 < nblk`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL[`nblk - 9`;`8`] DIVISION) THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `k = (nblk - 9) DIV 8` THEN ASM_ARITH_TAC);;

(* The output stores of the first 8 * (k + 1) blocks: the invariant's store *)
(* forall at i := k (taken from the definition, so it is the term the        *)
(* simulation keeps).  The prepretail stores nothing, so the forall passes   *)
(* through unchanged; the tail produces the remaining blocks.                *)
let wbn_out_forall =
  let full = list_mk_comb(wbn_core_applied, [`(nblk - 9) DIV 8`; `s:armstate`]) in
  let inv_cs = conjuncts (rhs(concl (REWRITE_CONV[wbn128_loop_inv_core] full))) in
  mk_abs(`s:armstate`, find is_forall inv_cs);;

let wbn_prepretail_post_ext =
  mk_abs(`s:armstate`,
    mk_conj(snd(dest_abs wbn_prepretail_post),
            snd(dest_abs wbn_out_forall)));;

(* The first tail block, global block 8 * (k + 1), from the input buffer:   *)
(* the ldr q9,[x0],#16 at 0xbd4 (step 247) loads it, and the tail reads it   *)
(* (eor3 at 0xbe4) before any reload.                                        *)
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

(* The extended seam post: the stores, the first tail block in Q9 and the   *)
(* raw counter, three adds past the loop head (s11, s20, s235): Q30 =        *)
(* gcm_ctr_raw (word (8 * k + 16)) ctr0, for the ivec write-back.            *)
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

(* The prepretail simulation, parameterized by the first-tail-block index   *)
(* bound (idx_lt_thm: ... ==> 8 * ((nblk - 9) DIV 8) + 8 < nblk): init at    *)
(* the invariant (i := k), the counter folds, the KEEPDATA bulk 21..180, the *)
(* wire-in at s182 (PL/PH/PM abbreviated), the reduce and the rest without  *)
(* simplification, the third counter add folded at s235, Q9 resolved at     *)
(* s246; the Q19 conjunct closes by WBN_Q19_PREPRETAIL_CLOSE_TAC.            *)
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
  (* the third add v30 (s235), in the unsimplified window: fold it, then    *)
  (* normalize 8*k+15+1 to 8*k+16; no later step writes v30                  *)
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

(* The prepretail, simulated once on the union band 9 <= nblk: its pre,     *)
(* post and steps are the same for the >=17 band and the 9..16 leg, and the *)
(* only band-dependent side condition (the Q9 index bound) holds for 9 <=   *)
(* nblk (WBN_Q9_INDEX_LT_9).                                                 *)
let WBN_PREPRETAIL_EXT2_UNIFIED =
  prove(wbn_prepretail_ext2_uni_goal, WBN_PREPRETAIL_EXT2_TAC WBN_Q9_INDEX_LT_9);;

(* the >=17 band, by strengthening the hypotheses *)
let WBN_PREPRETAIL_EXT2 =
  prove(wbn_prepretail_ext2_goal,
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC WBN_PREPRETAIL_EXT2_UNIFIED THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* From the seam to the core exit: the shifted tail.                         *)
(*                                                                           *)
(* The seam post wbn_prepretail_post_ext2 (pc+3032) feeds the shared tail    *)
(* back-leg WB_TAIL_GEN2_r at the shifted indices (shift_vals r):            *)
(* precondition weakening, no re-simulation.  The back-legs keep X9          *)
(* generic (return_value), so the shifted tail can return the whole-call     *)
(* count word (16 * nblk); X1, which differs, is not in their contract.      *)
(* The r-block tail also needs three disjointness facts the wide             *)
(* hypotheses do not carry (out_p against xi_p and ivec_p at the             *)
(* whole-buffer length, xi_p against ivec_p); they are side conditions       *)
(* here, implied by the exported ALLPAIRS premise.                           *)
(* ------------------------------------------------------------------------- *)

(* num_of_bytelist = num_of_wordlist on byte lists *)
let NUM_OF_BYTELIST_EQ_WORDLIST = prove
 (`!l:byte list. num_of_bytelist l = num_of_wordlist l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[num_of_bytelist; num_of_wordlist; DIMINDEX_8] THEN ARITH_TAC);;

(* Input-read restriction to a slice of length m (= 16*r) at 128*(k+1): the  *)
(* r-block shifted tail reads 16*r input bytes there, m kept symbolic under   *)
(* 128*(k+1)+m <= 16*nblk.  The slice of the list is a DIV then a MOD of its  *)
(* number (NUM_OF_WORDLIST_SUB_LIST), which READ_BYTES_DIV and READ_BYTES_MOD *)
(* turn back into a read.                                                     *)
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

(* the WB_TAIL_GEN2_r instantiation for residue r: wb_front_vars without
   nblk, then return_value; out_p, in_p, ibytes, xi and ctr0 are shifted
   past the first 8 * (k + 1) blocks, and the return value is the
   whole-call count *)
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
    `k8:int128`;`k9:int128`;`k10:int128`;`h:int128`;
    `word (16 * nblk):int64`];;

(* the 3 side-condition clauses (whole-length granularity). *)
let wbn_prep_to_end_extra_clauses =
  [`nonoverlapping (out_p:int64,16 * nblk) (xi_p:int64,16)`;
   `nonoverlapping (out_p:int64,16 * nblk) (ivec_p:int64,16)`;
   `nonoverlapping (xi_p:int64,16) (ivec_p:int64,16)`];;

(* list_of_seq splits at any point into a prefix + a shifted suffix. *)
let LIST_OF_SEQ_ADD = prove
 (`!m (f:num->A) n. list_of_seq f (m + n) =
        APPEND (list_of_seq f m) (list_of_seq (\i. f (m + i)) n)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; LIST_OF_SEQ; APPEND; ETA_AX];
    REWRITE_TAC[ADD_CLAUSES; LIST_OF_SEQ; APPEND] THEN
    AP_TERM_TAC THEN ASM_REWRITE_TAC[o_DEF]]);;

(* LIST_OF_SEQ_CLAUSES (in the base) only covers n=0..4; the r-block tag fold      *)
(* needs the explicit expansion up to n=8.  Each proved from the SUC recursion     *)
(* (num_CONV on the count down to a CLAUSES-known value, then APPEND).             *)
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

(* fold one gcm_ctr_inc into the running gcm_ctr_add offset (for the r>1 tail    *)
(* stores' inc^i towers in WBN_PREP_TO_END_FULL_r).                             *)
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
(* WBN_PREP_TO_END_FULL_r : the seam post fed to the shifted tail, delivering  *)
(* the FULL-nblk output/tag contract (not the r-block band_post).  Post =      *)
(* wbn_end_post: PC=pc+3756, the nblk-uniform output forall (aes9 XOR k10       *)
(* vocabulary, matching the ext2 seam's carried forall), the tag folded to      *)
(* list_of_seq cph nblk via GHASH_ACC_APPEND.                                   *)
(*                                                                             *)
(* Route: FRAME_SUBSUMED (narrow tail out-frame -> wide                         *)
(* wbn_front_C_tm), THEN ENSURES_POSTCONDITION_THM with the intermediate        *)
(*   inter_post_r = \s. (shifted band_post r) s /\ (ext2 first-8(k+1) forall) s  *)
(* splitting into: (1) inter_post_r ==> wbn_end_post [the tag-fold + store       *)
(* re-index math], and (2) ensures ext2post inter_post_r narrow_frame, closed    *)
(* by ENSURES_ADD_PRESERVED [narrow tail leg via INNER_TAIL_FEED_TAC + the       *)
(* first-blocks forall carried by read-over-write through the narrow frame,      *)
(* sound because the tail writes only bytes(out_p+128(k+1),16*r), disjoint       *)
(* from the first 128(k+1) output bytes].                                        *)
(* ------------------------------------------------------------------------- *)

(* the nblk-uniform end post (PC + byte count in X9 + output/tag/counter). *)
let wbn_end_post =
  let end_forall = `forall j. j < nblk
    ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
        word_xor (word_xor (bytes_to_int128 (SUB_LIST (16 * j,16) ibytes))
        (aes9 (gcm_ctr_inc_iter j ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9)) k10` in
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
    list_mk_conj [`read PC s = word (pc + 3756)`;
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

(* the narrow tail out-frame (writes only the last r output blocks) for shift r. *)
let wbn_tail_gen2 r =
  if r=1 then WB_TAIL_GEN2_1 else if r=2 then WB_TAIL_GEN2_2
  else if r=3 then WB_TAIL_GEN2_3 else if r=4 then WB_TAIL_GEN2_4
  else if r=5 then WB_TAIL_GEN2_5 else if r=6 then WB_TAIL_GEN2_6
  else if r=7 then WB_TAIL_GEN2_7 else WB_TAIL_GEN2_8;;
let wbn_narrow_frame r =
  el 3 (snd(strip_comb(snd(dest_imp(concl(SPECL (shift_vals r) (wbn_tail_gen2 r)))))));;

(* INNER_TAIL_FEED_TAC r tail_r: the post-FRAME_SUBSUMED inner half of           *)
(* WBN_PREP_TO_END_r_TAC (PRECONDITION_THM + feed the shifted tail); proves      *)
(* `ensures ext2post (shifted band_post r) narrow_frame` on its own.            *)
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
  (* ivec: with the Q30 conjunct carried in wbn_weak_q_at5_return r,
     the shifted tail precond demands read Q30 = gcm_ctr_raw (word 8)
     (gcm_ctr_add (word (8*(q+1))) ctr0); the EXT2 seam (ext2post, ASM_REWRITE'd in
     above) gives gcm_ctr_raw (word (8*q+16)) ctr0.  Absorb the prior add into the
     counter offset via GCM_CTR_RAW_ABSORB_NUM (8*(q+1)+8 = 8*q+16). *)
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

(* ------------------------------------------------------------------------- *)
(* WBN_PREP_TO_END_FULL_r for r=1..8 share one skeleton; the r-dependent       *)
(* hand-parts are packaged as OCaml `int -> tactic` closures below and driven  *)
(* by WBN_PREP_TO_END_FULL_r_TAC.                                              *)
(*                                                                             *)
(* KEY per-block algebra: for output block j = 8*(q+1)+i (0<=i<r), the         *)
(* seam-carried full-post value equals the r-block band store.  block_bridge   *)
(* proves that value identity STANDALONE (goal-form word_xor(word_xor cph      *)
(* aes9)k10 = store-form word_xor cph (aes128_encrypt ...)), reconciling:      *)
(*   - counter: gcm_ctr_inc_iter(8(q+1)+i) = gcm_ctr_add(word(8(q+1)+i)) =     *)
(*              gcm_ctr_inc^i (gcm_ctr_add(word 8(q+1)))  [GCM_CTR_INC_FOLD]    *)
(*   - cph slice: SUB_LIST(16*(8(q+1)+i),16) ibytes =                          *)
(*              SUB_LIST(16*i,16)(SUB_LIST(128(q+1),16*r) ibytes) [WBN_SUBLIST_SHIFT] *)
(*   - AES: GSYM AES128_XOR_ENCRYPT_RECONSTRUCT + WORD_RULE (XOR reassoc).     *)
(* block_close then reduces 16*i -> numeral (ARITH mul_red -- else the goal's  *)
(* SUB_LIST(16*i,..)/word(16*i) won't match the store's SUB_LIST(<16i>,..)/    *)
(* word <16i>) and reconciles the store address (i=0 flat, i>=1 nested).       *)
(* tag_fold folds the r-element explicit tag list to list_of_seq via           *)
(* LIST_OF_SEQ_ADD/GHASH_ACC_APPEND, closing each element by WBN_SUBLIST_SHIFT. *)
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

(* close one output block j = 8*(q+1)+i in the case-2 forall of FULL_r. *)
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

(* (A) the case-2 output forall for shift r. *)
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

(* (B) the tag fold: r-element explicit tag list -> list_of_seq cph nblk, split *)
(* at 8*(q+1) by the assumption nblk = 8*(q+1)+r (LIST_OF_SEQ_ADD).             *)
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

(* the full FULL_r tactic (r>=1): FRAME_SUBSUMED -> POSTCONDITION_THM with        *)
(* intermediate (shifted band_post /\ ext2 first-8(k+1) forall), split into        *)
(* [ (A) case-2 forall + (B) tag fold ] and [ ADD_PRESERVED: INNER_TAIL_FEED +     *)
(* carry the forall through the narrow tail writes ].                              *)
(* the intermediate post: shifted band_post r (of the SPECL'd tail) conjoined     *)
(* with the ext2 seam's first-8(k+1)-out-blocks forall (wbn_out_forall).         *)
let wbn_full_inter_post r =
  let band_post_r =
    el 2 (snd(strip_comb(snd(dest_imp(concl(SPECL (shift_vals r) (wbn_tail_gen2 r))))))) in
  mk_abs(`s:armstate`,
    mk_conj(snd(dest_abs band_post_r),
            snd(dest_abs wbn_out_forall)));;
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
        (* ivec: shifted band ivec = gcm_ctr_inc_iter r
           (gcm_ctr_add (word (8*(q+1))) ctr0) -> gcm_ctr_inc_iter nblk ctr0
           via ITER_ADD + ADD_COMPOSE + nblk = 8*(q+1)+r. *)
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
(* The suffix sim is BAND-AGNOSTIC                                            *)
(* (WBN_PREP_TO_END_FULL_r_TAC uses no `17<=nblk`/`9<=nblk` literal and no      *)
(* band-specific lemma; it only ABBREVs q=(nblk-9)DIV 8 symbolically), and it   *)
(* serves two consumer families (FULL_r on `17<=nblk`, FULL_916_r on            *)
(* `9<=nblk/\ nblk<=16`).  So prove it ONCE on the strictly-weaker UNIFIED      *)
(* band `9<=nblk` (WBN_PREP_TO_END_FREE_r), then derive both consumers by pure  *)
(* hyp-strengthening (the dispatchers wbn_full_thm/wbn_full_916_thm see the     *)
(* same statements).  ens is byte-identical across all three bands (only the    *)
(* front-hyps band conjunct differs), so MATCH_MP_TAC + ASM_ARITH closes.       *)
(* ------------------------------------------------------------------------- *)

(* wide front-hyps with the band conjunct `17<=nblk` weakened to `9<=nblk`. *)
let wbn_front_hyps_free_tm =
  let rec repl t = match t with
    | Comb(Comb(Const("/\\",_),a),b) -> mk_conj(repl a, repl b)
    | _ -> if t = `17 <= nblk` then `9 <= nblk` else t in
  repl wbn_front_hyps_wide_tm;;

(* the unified band-free (9<=nblk) full-post goal for a given r. *)
let wbn_prep_to_end_full_free_goal r =
  let nblk_eq = subst[mk_small_numeral r,`r_:num`]
                  `nblk = 8 * ((nblk - 9) DIV 8 + 1) + r_` in
  let hyps = end_itlist (curry mk_conj)
    (wbn_front_hyps_free_tm :: nblk_eq :: wbn_prep_to_end_extra_clauses) in
  let ens = list_mk_comb(`ensures arm`,
    [wbn_prepretail_post_ext2; wbn_end_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(hyps, ens));;

(* every r on the unified 9<=nblk band -- the SINGLE proof per r. *)
let WBN_PREP_TO_END_FREE_1 = prove(wbn_prep_to_end_full_free_goal 1, WBN_PREP_TO_END_FULL_r_TAC 1);;
let WBN_PREP_TO_END_FREE_2 = prove(wbn_prep_to_end_full_free_goal 2, WBN_PREP_TO_END_FULL_r_TAC 2);;
let WBN_PREP_TO_END_FREE_3 = prove(wbn_prep_to_end_full_free_goal 3, WBN_PREP_TO_END_FULL_r_TAC 3);;
let WBN_PREP_TO_END_FREE_4 = prove(wbn_prep_to_end_full_free_goal 4, WBN_PREP_TO_END_FULL_r_TAC 4);;
let WBN_PREP_TO_END_FREE_5 = prove(wbn_prep_to_end_full_free_goal 5, WBN_PREP_TO_END_FULL_r_TAC 5);;
let WBN_PREP_TO_END_FREE_6 = prove(wbn_prep_to_end_full_free_goal 6, WBN_PREP_TO_END_FULL_r_TAC 6);;
let WBN_PREP_TO_END_FREE_7 = prove(wbn_prep_to_end_full_free_goal 7, WBN_PREP_TO_END_FULL_r_TAC 7);;
let WBN_PREP_TO_END_FREE_8 = prove(wbn_prep_to_end_full_free_goal 8, WBN_PREP_TO_END_FULL_r_TAC 8);;

(* derive a banded consumer (wide OR 916) from the unified FREE_r by dropping the
   band down to 9<=nblk: MATCH_MP_TAC on the byte-identical ens, ASM_REWRITE the
   shared clauses, ASM_ARITH the band.  <0.1s, hyps=0.  Same idiom as
   WBN_PREPRETAIL_EXT2_916 below. *)
let wbn_prep_to_end_full_derive_tac free_thm =
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC free_thm THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;;

(* the full-post legs, DERIVED from the unified FREE_r (no re-sim). *)
let WBN_PREP_TO_END_FULL_1 = prove(wbn_prep_to_end_full_goal 1, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_1);;
let WBN_PREP_TO_END_FULL_2 = prove(wbn_prep_to_end_full_goal 2, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_2);;
let WBN_PREP_TO_END_FULL_3 = prove(wbn_prep_to_end_full_goal 3, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_3);;
let WBN_PREP_TO_END_FULL_4 = prove(wbn_prep_to_end_full_goal 4, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_4);;
let WBN_PREP_TO_END_FULL_5 = prove(wbn_prep_to_end_full_goal 5, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_5);;
let WBN_PREP_TO_END_FULL_6 = prove(wbn_prep_to_end_full_goal 6, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_6);;
let WBN_PREP_TO_END_FULL_7 = prove(wbn_prep_to_end_full_goal 7, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_7);;
let WBN_PREP_TO_END_FULL_8 = prove(wbn_prep_to_end_full_goal 8, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_8);;

(* ------------------------------------------------------------------------- *)
(* WBN_PREP_TO_END: the 8-way case split on r = 1+(nblk-9) MOD 8.               *)
(* From the ext2 seam post to the full nblk-uniform wbn_end_post, under         *)
(* 9 <= nblk + the 3 side-conditions.  Each residue rr in {0..7} dispatches to   *)
(* WBN_PREP_TO_END_FULL_(rr+1); the per-branch length hyp                        *)
(* nblk = 8*((nblk-9)DIV 8 + 1) + (rr+1) follows by ARITH from the DIVISION      *)
(* identity + 9 <= nblk.                                                         *)
(* ------------------------------------------------------------------------- *)

let wbn_full_thm = Array.of_list
  [WBN_PREP_TO_END_FULL_1;  (* index 0 unused-ish; use r directly 1..8 *)
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

(* the 9..16 hyp band: wbn_front_hyps_wide_tm with 17<=nblk -> 9<=nblk/\nblk<=16 *)
let wbn_front_hyps_916_tm =
  let rec repl t = match t with
    | Comb(Comb(Const("/\\",_),a),b) -> mk_conj(repl a, repl b)
    | _ -> if t = `17 <= nblk` then `9 <= nblk /\ nblk <= 16` else t in
  repl wbn_front_hyps_wide_tm;;

(* postcond target for the front-916 leg = wbn_core_applied 0 at PC 0x7fc. *)
let wbn_entry_post_916 =
  mk_abs(`s:armstate`,
    list_mk_conj[
      `aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc`;
      `read PC s = word (pc + 2044)`;
      mk_comb(mk_comb(wbn_core_applied,`0:num`),`s:armstate`)]);;

let wbn_front_to_prep_916_goal =
  let ens = list_mk_comb(`ensures arm`,[wbn_front_P_tm; wbn_entry_post_916; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_916_tm, ens));;

(* FRONT-916: the shared prefix WBN_FRONT_PREFIX_EXT (pc+0x1c to the 0x3b0
   b.ge, with the loop constants R) via ENSURES_TRANS_SIMPLE, then step 230:
   the b.ge is taken for 9..16, since the cmp x0,x5 at 0x3a8 compares
   X0 = in_p + 128 with X5 = in_p + 128 * ((nblk - 1) DIV 8) = in_p + 128
   (NF = VF = F), landing at 0x7fc = wbn_core_applied 0.  The invariant core,
   the htable and the ABI frame are unfolded before the step, so the htable
   reads propagate through it (the folded htable_mem_dec is not tracked by the
   stepper) and the final state discharges the frame; the counters close as
   gcm_ctr_add lanes, Q19 as the reversed tag over no blocks and Q30 as the
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

(* PREPRETAIL-916 (9..16 band), derived (no sim) from
   WBN_PREPRETAIL_EXT2_UNIFIED by hyp-strengthening (see the note at
   WBN_PREPRETAIL_EXT2_UNIFIED): the shared sim ran on the 9<=nblk band that
   already subsumes 9..16, so this is a pure MATCH_MP + ASM_ARITH close. *)
let wbn_prepretail_ext2_916_goal = mk_wbn_prepretail_goal wbn_front_hyps_916_tm;;

let WBN_PREPRETAIL_EXT2_916 =
  prove(wbn_prepretail_ext2_916_goal,
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC WBN_PREPRETAIL_EXT2_UNIFIED THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* FRONT-916 ; PREPRETAIL-916 composed to the ext2 seam (pc+0x1c -> pc+3032).       *)
(* The PRECONDITION bridge collapses (nblk-9)DIV8 to 0 (q=0 for 9..16), matching     *)
(* the front-916 postcond (wbn_core_applied 0) to the prepretail-916 precond.        *)
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

(* WBN_PREP_TO_END_916: pc+3032 -> pc+3756 for the 9..16 band.  Same 8-way r split *)
(* as WBN_PREP_TO_END but with the 9..16 hyp band; dispatches to the FULL_916_r     *)
(* legs (r-block seam->band reconciliation, symbolic in q, q=0 here), each derived  *)
(* from the unified FREE_r like FULL_r.  The dispatcher is the WBN_PREP_TO_END      *)
(* 8-way rr=(nblk-9)MOD 8 split over the FULL_916 array.                            *)

(* 916-banded full-post goal (9..16 band; otherwise identical to *)
(* wbn_prep_to_end_full_goal). *)
let wbn_prep_to_end_full_916_goal r =
  let nblk_eq = subst[mk_small_numeral r,`r_:num`]
                  `nblk = 8 * ((nblk - 9) DIV 8 + 1) + r_` in
  let hyps = end_itlist (curry mk_conj)
    (wbn_front_hyps_916_tm :: nblk_eq :: wbn_prep_to_end_extra_clauses) in
  let ens = list_mk_comb(`ensures arm`,
    [wbn_prepretail_post_ext2; wbn_end_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(hyps, ens));;

(* DERIVED from the unified FREE_r sims proved once above, with no re-simulation. *)
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

(* WBN_FRONT_TO_END_916: the full 9..16 front->exit chain, pc+0x1c -> pc+3756. *)
(* FRONT_TO_PREP_EXT2_916 ; PREP_TO_END_916 via ENSURES_TRANS_SIMPLE.          *)
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
(* The main-loop body: one iteration, 0x3b4..0x7f8 (274 steps).              *)
(*                                                                           *)
(* From the core at i (PC pc+948) to the core at i + 1, with PC pc+948 if    *)
(* i + 1 < k and the prepretail pc+2044 otherwise.  The body runs 8 AES-128  *)
(* keystreams, folds the lagging 8-block group into GHASH, advances the      *)
(* counter 8i+13 -> 8i+21, stores 8 plaintext blocks and loads the next 8    *)
(* ciphertext blocks.  Cut points: the counter folds, taken by the steppers  *)
(* (rev32 at s10, s15, s22, s196, s209, s226, s250, s270, add v30 at s11,    *)
(* s16, s187, s198, s217, s234, s251, s271); the GHASH wire-in at s197       *)
(* (PL/PH/PM abbreviated, the reduce s212..s262 on them); the ldp's of the   *)
(* next group resolved at load (s222, s223, s227, s231) from the input       *)
(* buffer; the cmp x0,x5 at s265 and the signed b.lt at s274                 *)
(* (WB_PTRCMP_FLAGS, WBN_PC_BRIDGE).                                         *)
(* ------------------------------------------------------------------------- *)

(* the next group's blocks are in range: 8 * (i + 1) + m < nblk, and its
   raw ciphertext lanes read from the input buffer *)
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
   [ASM_REWRITE_TAC[];
    DISCH_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(SPEC_ALL WBN_RAWCT_BOUND) THEN ASM_SIMP_TAC[]]);;

(* RAWCT_LEMMA_AT sprev: the WBN_RAWCT_READ !m lemma at state sprev *)
let RAWCT_LEMMA_AT sprev : tactic =
  SUBGOAL_THEN
    (subst[mk_var(sprev,`:armstate`),`s:armstate`]
      `!m. m < 8 ==> read (memory :> bytes128 (word_add in_p (word (16 * (8*(i+1)+m))))) s =
                     bytes_to_int128 (SUB_LIST (16 * (8*(i+1)+m), 16) ibytes)`)
    ASSUME_TAC THENL
   [MATCH_MP_TAC WBN_RAWCT_READ THEN ASM_REWRITE_TAC[]; ALL_TAC];;

(* RESOLVE_QREG_C qreg scur m: resolve read qreg scur = read (memory :>
   bytes128 ADDR) sload, the raw read an ldp leaves, against the raw lemma
   at sload (the load-input state); PURE_ONCE_REWRITE keeps the m = 0
   index 8*(i+1)+0 unreduced for the ACCEPT *)
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

(* NEWBLK_CLOSE_TAC: close one new-block leg of the store-forall (j = 8*(i+1)+m,
   0<=m<8).  Canonicalize block indices 8*(i+1)+m -> 8*i+(8+m), normalize both
   store-readback address forms (out_p+(128*(i+1)+16m) and (out_p+128*(i+1))+16m)
   to the flat goal form, fire the readback, then fold the plaintext
   (GSYM aes9 + GCM_CTR_INC_ITER_AS_ADD) and bridge the SUB_LIST index. *)
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
  (* Fire the store-readback hyp (ASM_REWRITE) BEFORE folding the raw
     aese/aesmc tower: with GSYM aes9 first, the goal LHS is still
     `read(mem) s274` (tower not yet substituted), so the fold has nothing to
     match and REFL_TAC fails on the 8 new-block legs. *)
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


(* premises of WB_PTRCMP_FLAGS at the back-edge: X0=in_p+128*(i+2) (a),
   X5=128*((nblk-1)DIV8)+in_p (d); both offsets < 2^63 from val in_p+16*nblk. *)
let WBN_PTRCMP_PREMS = prove
 (`val (in_p:int64) + 16 * nblk < 2 EXP 63 /\ i < (nblk - 9) DIV 8
   ==> val (in_p:int64) + 128 * (i + 2) < 2 EXP 63 /\
       val (in_p:int64) + 128 * (nblk - 1) DIV 8 < 2 EXP 63`,
  STRIP_TAC THEN
  MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN
  MP_TAC(SPECL [`nblk - 9`; `8`] DIVISION) THEN ASM_ARITH_TAC);;

(* word distributes over the back-edge if *)
let WBN_PC_IF = prove
 (`(if b then word (pc + 948) else word (pc + 2044)):int64 =
   word (if b then pc + 948 else pc + 2044)`,
  COND_CASES_TAC THEN REWRITE_TAC[]);;

(* X0 and X2 after the four 32-byte post-increments of an iteration *)
let WBN_PTR_ADV = WORD_RULE
  `word_add (word_add p (word (128 * (i + 1)))) (word 128):int64 =
   word_add p (word (128 * (i + 2)))`;;

(* THE LOOP BODY: one iteration, every i < (nblk - 9) DIV 8. *)
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

(* THE MAIN LOOP, PC = pc+948 /\ core 0 to PC = pc+2044 /\ core k: the
   skeleton WBN_MAIN_LOOP_OF_BODY applied to the body. *)
let WBN_MAIN_LOOP_raw = prove(wbn_main_loop_goal,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun hyps -> MATCH_MP_TAC (MP (SPEC_ALL WBN_MAIN_LOOP_OF_BODY) hyps)) THEN
  FIRST_ASSUM(fun hyps -> ACCEPT_TAC (MP (SPEC_ALL WBN_LOOP_BODY) hyps)));;

(* ------------------------------------------------------------------------- *)
(* The >=17 chain: the front to the loop head, the loop, the prepretail and  *)
(* the shifted tail, pc+0x1c to the core exit pc+3756.                       *)
(* ------------------------------------------------------------------------- *)

(* the loop then the prepretail: loop head pc+948 to the seam pc+3032 *)
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

(* the front, the loop and the prepretail: pc+0x1c to the seam pc+3032 *)
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

(* WBN_FRONT_TO_END: the whole >=17 chain, pc+0x1c to pc+3756, with the end  *)
(* post wbn_end_post; the three side conditions of the shifted tail ride the *)
(* antecedent outward.                                                       *)
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
(* The NIST tag and output bridges at a symbolic block count: the end        *)
(* post's GHASH tag is nist_ghash over the NIST input blocks, and its        *)
(* per-block store forall is the whole-buffer gcm_dec128_pt_bytes list.      *)
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

(* The full L1 output bridge: wbn_end_post's per-block store forall            *)
(* (word_xor(word_xor cph aes9..)k10) collapses to                              *)
(* byte_list_at(gcm_dec128_pt_bytes(16*nblk)..) over the whole buffer.  The     *)
(* symbolic-nblk analogue of prove_wb_wrapper's BYTE_LIST_AT_WHOLE_CTR leg.     *)
(* 128*nblk < 2 EXP 64 (from the chain hyps) gives val(word(16*nblk))=16*nblk.  *)
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
(* WBN_DEC_CORE_BYTELIST: the core spine, pc+28 to pc+3756, for every        *)
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
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p nblk ibytes rk H
    tag0 ctr0.
    1 <= nblk /\
    128 * nblk < 2 EXP 64 /\
    val in_p + 16 * nblk < 2 EXP 63 /\
    LENGTH ibytes = 16 * nblk /\
    LENGTH rk = 11 /\
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16]
    [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,176; htbl_p,192; stackpointer,80] /\
    PAIRWISE nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16] /\
    ALL (nonoverlapping (stackpointer,80))
    [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,176; htbl_p,192]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
              read PC s = word (pc + 28) /\
              read SP s = stackpointer /\
              C_ARGUMENTS
                [in_p; word (128 * nblk); out_p; xi_p; ivec_p; key_p; htbl_p]
                s /\
              byte_list_at ibytes in_p (word (16 * nblk)) s /\
              read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
              read (memory :> bytes128 ivec_p) s = ctr0 /\
              wordlist_from_memory (key_p,11) s = rk /\
              htable_mem_8 (ghash_twist H) htbl_p s)
         (\s. read PC s = word (pc + 3756) /\
              read X9 s = word (16 * nblk) /\
              byte_list_at (gcm_dec128_pt_bytes (16 * nblk) ibytes ctr0 rk) out_p
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
       NONOVERLAPPING_SYM (permutative, so HOL rewrites in order), and the band *)
    ASM_CASES_TAC `nblk <= 16` THENL
     [MATCH_MP_TAC WBN_FRONT_TO_END_916; MATCH_MP_TAC WBN_FRONT_TO_END] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_SYM]) THEN
    ASM_REWRITE_TAC[NONOVERLAPPING_SYM] THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* WBN_DEC_SUBROUTINE_BYTELIST: the ABI wrapper spine, for bit_len =         *)
(* 128 * nblk and any nblk including 0.  For nblk >= 1 it is the stock       *)
(* ARM_ADD_RETURN_STACK_TAC wrapper of WBN_DEC_CORE_BYTELIST at the          *)
(* in-frame SP: the entry guard (cbz x1; tst x1,#127; b.ne) falls through   *)
(* and the prologue spills d8..d15 to the 80-byte frame (steps 1..7), the    *)
(* core is one big step from pc+0x1c to pc+0xeac, and the epilogue           *)
(* (mov x0,x9; the d-register reloads; ret) runs steps 9..14.                *)
(* For nblk = 0 the cbz is taken and the call returns 0 through the          *)
(* reject path.                                                              *)
(* ------------------------------------------------------------------------- *)

let WBN_DEC_SUBROUTINE_BYTELIST = prove
   (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p nblk ibytes rk H
      tag0 ctr0 returnaddress.
      128 * nblk < 2 EXP 64 /\
      val in_p + 16 * nblk < 2 EXP 63 /\
      LENGTH ibytes = 16 * nblk /\
      LENGTH rk = 11 /\
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16]
      [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,176; htbl_p,192;
       word_sub stackpointer (word 80),80] /\
      PAIRWISE nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16] /\
      ALL (nonoverlapping (word_sub stackpointer (word 80),80))
      [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,176; htbl_p,192]
      ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
               read PC s = word pc /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS
               [in_p; word (128 * nblk); out_p; xi_p; ivec_p; key_p; htbl_p]
               s /\
               byte_list_at ibytes in_p (word (16 * nblk)) s /\
               read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,11) s = rk /\
               htable_mem_8 (ghash_twist H) htbl_p s)
          (\s. read PC s = returnaddress /\
               C_RETURN s = word (16 * nblk) /\
               byte_list_at (gcm_dec128_pt_bytes (16 * nblk) ibytes ctr0 rk) out_p
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
  let EXEC = AES128_GCM_DEC_ALT_EXEC in
  (* nblk >= 1 in the shape ARM_ADD_RETURN_STACK_TAC takes: the statement
     below with stackpointer and returnaddress quantified last, and with the
     input byte bound and the facts that make the entry guard fall through
     (cbz x1 not taken; tst x1,#127 sets Z for the b.ne) as hypotheses, so
     that the prologue steps can use them *)
  let WBN_DEC_SUBROUTINE_NZ = prove
   (`!pc in_p out_p xi_p ivec_p key_p htbl_p nblk ibytes rk H tag0 ctr0
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
        ALLPAIRS nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16]
        [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,176; htbl_p,192;
         word_sub stackpointer (word 80),80] /\
        PAIRWISE nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16] /\
        ALL (nonoverlapping (word_sub stackpointer (word 80),80))
        [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,176; htbl_p,192]
        ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
                 read PC s = word pc /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS
                 [in_p; word (128 * nblk); out_p; xi_p; ivec_p; key_p; htbl_p]
                 s /\
                 byte_list_at ibytes in_p (word (16 * nblk)) s /\
                 read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
                 read (memory :> bytes128 ivec_p) s = ctr0 /\
                 wordlist_from_memory (key_p,11) s = rk /\
                 htable_mem_8 (ghash_twist H) htbl_p s)
            (\s. read PC s = returnaddress /\
                 C_RETURN s = word (16 * nblk) /\
                 byte_list_at (gcm_dec128_pt_bytes (16 * nblk) ibytes ctr0 rk) out_p
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
    REWRITE_TAC[byte_list_at; wordlist_from_memory; HTABLE_MEM_8_FLAT; DIMINDEX_128] THEN
    ARM_ADD_RETURN_STACK_TAC ~pre_post_nsteps:(7,5) EXEC
     (REWRITE_RULE[byte_list_at; wordlist_from_memory; HTABLE_MEM_8_FLAT; DIMINDEX_128;
                   ARITH_RULE `1 <= n <=> ~(n = 0)`]
       (GENL [`pc:num`; `in_p:int64`; `out_p:int64`; `xi_p:int64`; `ivec_p:int64`;
              `key_p:int64`; `htbl_p:int64`; `nblk:num`; `ibytes:byte list`;
              `rk:int128 list`; `H:int128`; `tag0:int128`; `ctr0:int128`;
              `stackpointer:int64`]
         (SPEC_ALL WBN_DEC_CORE_BYTELIST)))
     `[D8; D9; D10; D11; D12; D13; D14; D15]` 80) in
  REPEAT STRIP_TAC THEN
  (* nblk = 0: the entry cbz x1 (0x0) is TAKEN before the prologue, so the
     function returns 0 in X0 touching no memory (mov w0,#0; ret @0xec4);
     d8-d15/SP are untouched (never spilled).  The output byte list is empty
     (byte_list_at over word 0 is vacuous) and the tag is unchanged
     (nist_ghash H tag0 [] = tag0).  Mirrors the encrypt nb=0 leg. *)
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

(* ------------------------------------------------------------------------- *)
(* The exported contracts, in the shared AES-GCM vocabulary.                 *)
(*                                                                           *)
(* AES128_GCM_DEC_ALT_CORRECT (the core, pc + 28 to pc + 3756) and           *)
(* AES128_GCM_DEC_ALT_NOIBT_SUBROUTINE_CORRECT (the AAPCS64 wrapper, any     *)
(* bit_len), both about the trimmed code, are lifted from the spines by      *)
(* WBN_EXPORT_FROM_SPINE_TAC, without re-simulation: the key words, the      *)
(* GHASH key and the counter block are pinned to the FIPS-197 / NIST         *)
(* convention and the input and output are restated per block.               *)
(* AES128_GCM_DEC_ALT_SUBROUTINE_CORRECT, about the full code, follows from  *)
(* the NOIBT one by ARM_ADD_IBT_RULE.  The machine code writes every one of  *)
(* the 32 vector registers; beyond the ABI frame, the core frame lists       *)
(* Q8-Q15 (WB_CORE_FRAME_EQ below).                                          *)
(* ------------------------------------------------------------------------- *)

(* The frame of the two core theorems.  MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ *)
(* ABI already covers Q0-Q7, Q16-Q31 and the top halves of Q8-Q15, so beyond  *)
(* it the core theorems list only Q8-Q15, whose bottom halves d8-d15 the      *)
(* prologue saves before the core and the epilogue restores after it.  This  *)
(* is the same frame as the internal spines', which list all of Q0-Q31: the   *)
(* two are equal, so stating the shorter one weakens nothing, and the proofs *)
(* rewrite it back to the spines' form.                                       *)
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

(* THE EXPORTED CORE CONTRACT (after the prologue, bit_len = 128 * nblk).    *)
let AES128_GCM_DEC_ALT_CORRECT = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p nblk inblock rk
    tag0 nonce c.
    1 <= nblk /\
    128 * nblk < 2 EXP 64 /\
    val in_p + 16 * nblk < 2 EXP 63 /\
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16]
    [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,176; htbl_p,192; stackpointer,80] /\
    PAIRWISE nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16] /\
    ALL (nonoverlapping (stackpointer,80))
    [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,176; htbl_p,192]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
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
              wordlist_from_memory (key_p,11) s =
              MAP (word_reversefields 8) rk /\
              htable_mem_8 (ghash_twist (aes128_cipher (word 0) rk)) htbl_p s)
         (\s. read PC s = word (pc + 3756) /\
              read X9 s = word (16 * nblk) /\
              (!j. j < nblk
                   ==> read (memory :> bytes128
                              (word_add out_p (word (16 * j)))) s =
                       word_xor (aes_ctr_block aes128_cipher c nonce rk j)
                                (inblock j)) /\
              read (memory :> bytes128 xi_p) s =
              word_reversefields 8
              (nist_ghash (aes128_cipher (word 0) rk) tag0
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
    [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,176; htbl_p,192;
     word_sub stackpointer (word 80),80] /\
    PAIRWISE nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16] /\
    ALL (nonoverlapping (word_sub stackpointer (word 80),80))
    [word pc, LENGTH aes128_gcm_dec_alt_tmc; in_p,16 * nblk; key_p,176; htbl_p,192]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
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
              wordlist_from_memory (key_p,11) s =
              MAP (word_reversefields 8) rk /\
              htable_mem_8 (ghash_twist (aes128_cipher (word 0) rk)) htbl_p s)
         (\s. read PC s = returnaddress /\
              C_RETURN s = word (16 * nblk) /\
              (!j. j < nblk
                   ==> read (memory :> bytes128
                              (word_add out_p (word (16 * j)))) s =
                       word_xor (aes_ctr_block aes128_cipher c nonce rk j)
                                (inblock j)) /\
              read (memory :> bytes128 xi_p) s =
              word_reversefields 8
              (nist_ghash (aes128_cipher (word 0) rk) tag0
              (list_of_seq (nist_input_block inblock) nblk)) /\
              read (memory :> bytes128 ivec_p) s =
              word_reversefields 8 (ctr_block nonce (nblk + c)))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
          [memory :> bytes (out_p,16 * nblk); memory :> bytes (xi_p,16);
           memory :> bytes (ivec_p,16);
           memory :> bytes (word_sub stackpointer (word 80),80)])`,
  WBN_EXPORT_FROM_SPINE_TAC WBN_DEC_SUBROUTINE_BYTELIST);;

(* THE EXPORTED SUBROUTINE CONTRACT (the AAPCS64-callable headline result),
   for an arbitrary bit_len, first for the trimmed code, the code of a
   -DNO_IBT build.  gcm_wb_blocks bit_len is the number of
   blocks processed, and every data-dependent clause is indexed by it, so one
   postcondition describes all three paths:
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
let AES128_GCM_DEC_ALT_NOIBT_SUBROUTINE_CORRECT = prove
 (`!pc stackpointer in_p bit_len out_p xi_p ivec_p key_p htbl_p inblock rk
    tag0 nonce c returnaddress.
    val in_p + 16 * gcm_wb_blocks bit_len < 2 EXP 63 /\
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping
    [out_p,16 * gcm_wb_blocks bit_len; xi_p,16; ivec_p,16]
    [word pc, LENGTH aes128_gcm_dec_alt_tmc;
     in_p,16 * gcm_wb_blocks bit_len; key_p,176; htbl_p,192;
     word_sub stackpointer (word 80),80] /\
    PAIRWISE nonoverlapping
    [out_p,16 * gcm_wb_blocks bit_len; xi_p,16; ivec_p,16] /\
    ALL (nonoverlapping (word_sub stackpointer (word 80),80))
    [word pc, LENGTH aes128_gcm_dec_alt_tmc;
     in_p,16 * gcm_wb_blocks bit_len; key_p,176; htbl_p,192]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
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
              wordlist_from_memory (key_p,11) s =
              MAP (word_reversefields 8) rk /\
              htable_mem_8 (ghash_twist (aes128_cipher (word 0) rk)) htbl_p s)
         (\s. read PC s = returnaddress /\
              C_RETURN s = word (16 * gcm_wb_blocks bit_len) /\
              (!j. j < gcm_wb_blocks bit_len
                   ==> read (memory :> bytes128
                              (word_add out_p (word (16 * j)))) s =
                       word_xor (aes_ctr_block aes128_cipher c nonce rk j)
                                (inblock j)) /\
              read (memory :> bytes128 xi_p) s =
              word_reversefields 8
              (nist_ghash (aes128_cipher (word 0) rk) tag0
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
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `val(bit_len:int64) MOD 128 = 0` THENL
   [(* Whole blocks, including zero: WBN_DEC_VALID_CALL_CORRECT at
       nblk = gcm_wb_blocks bit_len, where word (128 * nblk) is
       word (val bit_len) = bit_len by GCM_WB_BLOCKS_VALID. *)
    MP_TAC(INST [`gcm_wb_blocks bit_len`,`nblk:num`]
                (SPEC_ALL WBN_DEC_VALID_CALL_CORRECT)) THEN
    ASM_SIMP_TAC[GSYM GCM_WB_BLOCKS_VALID; WORD_VAL; VAL_BOUND_64];
    (* A non-multiple of 128: no blocks (gcm_wb_blocks bit_len = 0); cbz
       falls through (val bit_len <> 0), tst/b.ne rejects (the low seven
       bits are not all zero), and no memory is touched. *)
    SUBGOAL_THEN `~(val(bit_len:int64) = 0) /\
                  ~(val(word_and (bit_len:int64) (word 127)) = 0)`
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
 (`!pc stackpointer in_p bit_len out_p xi_p ivec_p key_p htbl_p inblock rk
    tag0 nonce c returnaddress.
    val in_p + 16 * gcm_wb_blocks bit_len < 2 EXP 63 /\
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping
    [out_p,16 * gcm_wb_blocks bit_len; xi_p,16; ivec_p,16]
    [word pc, LENGTH aes128_gcm_dec_alt_mc;
     in_p,16 * gcm_wb_blocks bit_len; key_p,176; htbl_p,192;
     word_sub stackpointer (word 80),80] /\
    PAIRWISE nonoverlapping
    [out_p,16 * gcm_wb_blocks bit_len; xi_p,16; ivec_p,16] /\
    ALL (nonoverlapping (word_sub stackpointer (word 80),80))
    [word pc, LENGTH aes128_gcm_dec_alt_mc;
     in_p,16 * gcm_wb_blocks bit_len; key_p,176; htbl_p,192]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_mc /\
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
              wordlist_from_memory (key_p,11) s =
              MAP (word_reversefields 8) rk /\
              htable_mem_8 (ghash_twist (aes128_cipher (word 0) rk)) htbl_p s)
         (\s. read PC s = returnaddress /\
              C_RETURN s = word (16 * gcm_wb_blocks bit_len) /\
              (!j. j < gcm_wb_blocks bit_len
                   ==> read (memory :> bytes128
                              (word_add out_p (word (16 * j)))) s =
                       word_xor (aes_ctr_block aes128_cipher c nonce rk j)
                                (inblock j)) /\
              read (memory :> bytes128 xi_p) s =
              word_reversefields 8
              (nist_ghash (aes128_cipher (word 0) rk) tag0
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
    aes128_gcm_dec_alt_mc aes128_gcm_dec_alt_tmc
    AES128_GCM_DEC_ALT_NOIBT_SUBROUTINE_CORRECT));;
(* ------------------------------------------------------------------------- *)
(* The exported theorem at the all-zero key.  With rk the FIPS-197 schedule  *)
(* of that key, the key table precondition of                                *)
(* AES128_GCM_DEC_ALT_SUBROUTINE_CORRECT rewrites, by                        *)
(* HTABLE_MEM_8_AESAVS_ZERO_KEY_128 at the top of this file, to the twelve   *)
(* 16-byte entries that gcm_init_v8 writes for the key, which are also the   *)
(* bytes the C test aes_gcm_htable checks.  So the table described by the    *)
(* exported statement itself, not only by the vocabulary it uses, is the     *)
(* real one; the load fails here if the precondition is not of that form.    *)
(* ------------------------------------------------------------------------- *)

let AES128_GCM_DEC_ALT_ZERO_KEY_CORRECT =
  let th = PURE_REWRITE_RULE[HTABLE_MEM_8_AESAVS_ZERO_KEY_128]
   (INST [`AESAVS_ZERO_KEY_128_SCHEDULE`,`rk:int128 list`]
     (SPEC_ALL AES128_GCM_DEC_ALT_SUBROUTINE_CORRECT)) in
  if can (find_term (fun t -> is_const t && fst(dest_const t) = "htable_mem_8"))
         (concl th)
  then failwith "AES128_GCM_DEC_ALT_ZERO_KEY_CORRECT: table not rewritten"
  else GEN_ALL th;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let EXEC = AES128_GCM_DEC_ALT_EXEC;;

(* ---- quiet stepper: the default one logs a line per state, and these legs
   run several hundred steps each ---- *)
let ARM_QSTEP_TAC th s =
  ARM_STEP_TAC th [] s None (K STRIP_TAC) THEN DISCARD_OLDSTATE_TAC s THEN CLARIFY_TAC;;
let ARM_QSTEPS_TAC th snums = MAP_EVERY (ARM_QSTEP_TAC th) (statenames "s" snums);;

(* ---- GENERAL affine word_sub cancellation (NO WORD_BLAST) ----
   For a `word_sub P Q` subterm whose only free int64 var is a single register base
   x (in_p/out_p/...), the difference P-Q is a constant independent of x. Prove
   `word_sub P Q = word_sub P[x:=0] Q[x:=0]` by WORD_RULE (the x-dependence cancels),
   then WORD_REDUCE the RHS to a numeral `word k`.  Covers the 9-16 loop-enter shape
   `word_sub in_p (word_add (word 128) in_p)` as well as the plain tail compares. *)
let affine_cancel_thm t =
  match t with
  | Comb(Comb(Const("word_sub",_),_),_) ->
    let fv = filter (fun v -> type_of v = `:int64` && is_var v) (frees t) in
    (match fv with
     | [x] ->
       let t0 = subst [`word 0:int64`, x] t in
       let step1 = WORD_RULE (mk_eq(t, t0)) in
       CONV_RULE (RAND_CONV WORD_REDUCE_CONV) step1     (* |- word_sub P Q = word k *)
     | _ -> failwith "affine_cancel_thm: not exactly one int64 var")
  | _ -> failwith "affine_cancel_thm: not word_sub";;

(* Collect every affine word_sub in goal+asms, cancel it, rewrite, then reduce the
   now-concrete PC if-condition. *)
let WB_TAIL_RESOLVE_TAC : tactic = fun (asl,w) ->
  let is_sub tm = match tm with
    | Comb(Comb(Const("word_sub",_),_),_) ->
        length (filter (fun v -> type_of v = `:int64` && is_var v) (frees tm)) = 1
    | _ -> false in
  let all = itlist (fun (_,th) acc -> concl th :: acc) asl [w] in
  let subs = setify (itlist (fun t acc -> find_terms is_sub t @ acc) all []) in
  let cancel_thms = mapfilter affine_cancel_thm subs in
  (RULE_ASSUM_TAC(REWRITE_RULE cancel_thms) THEN
   (* reflexive branch at 0x340: ival in_p - ival in_p / word_sub X X = 0 *)
   RULE_ASSUM_TAC(REWRITE_RULE[INT_SUB_REFL; WORD_SUB_REFL; VAL_WORD_0; IVAL_WORD_0]) THEN
   RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV WORD_REDUCE_CONV)) THEN
   RULE_ASSUM_TAC(CONV_RULE(TRY_CONV INT_REDUCE_CONV)) THEN
   RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(DEPTH_CONV NUM_EQ_CONV))) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[NOT_CLAUSES; COND_CLAUSES]) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[])) (asl,w);;

(* ---- extract (current-state index, PC offset) from the goal's PC assumption.
   off: >=0 concrete pc+off (or bare word off); -2 symbolic if-term (needs resolve);
        -3 no PC assumption found. ---- *)
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
   Steps ARM instrs one at a time from the current state; when the PC becomes a
   symbolic if-term, applies WB_TAIL_RESOLVE_TAC to make it concrete, then steps;
   stops when PC = word (pc + target).

   This is GEN_PROVE_SAFETY_SPEC_TAC's own driver loop (in common/consttime.ml:
   find the `read PC` assumption, compare its RHS to the destination, else take one
   more step) with one addition, which is why the stock tactic cannot be called here:
   the nblk dispatch leaves the PC a symbolic if-term part-way through a leg, and the
   stock loop has no resolver for that -- it only ever compares for equality, so it
   would stop, having neither reached the destination nor made progress.  Resolving
   such a PC by hand is what BIGNUM_EMONTREDC_8N_CORRECT does in the corpus
   (UNDISCH the if-term PC, rewrite it concrete, DISCH, keep stepping).  Here that
   would have to be repeated at every dispatch point of all 24 driven legs -- the
   sixteen concrete nblk bands and the eight tail residues -- so the resolve step is
   folded into the loop instead of being written out per band. ---- *)
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

(* ---- the opening of every simulated leg: unfold the list wrappers of the
   nonoverlapping hypotheses (keeping nonoverlapping itself FOLDED, with the
   code length as a numeral), split the resulting conjunctions into single
   assumptions, init state s0 ---- *)
let LEG_INIT_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[ALL; ALLPAIRS; PAIRWISE; MAP; WB_MC_LEN]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  ENSURES_INIT_TAC "s0";;

(* ---- UNIFORM concrete-band closer: open, then DRIVE from s0 to pc+3756, finalize.
   Works for ANY concrete nblk (1..16): every branch condition is concrete arithmetic
   the resolver reduces directly, so no band-specific step count or front prefix.
   The symbolic NBLK_ARITH lemmas are only needed for the symbolic >=17 leg. ---- *)
let concrete_band_close_tac =
  LEG_INIT_TAC THEN
  DRIVE_TAC 3756 700 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ---- the case split shared by the band and residue dispatches: assert
   x = lo \/ ... \/ x = hi, proved by side_tac, and leave the cases in order.
   BOUNDS_ARITH_TAC proves such a disjunction from the named bounds alone,
   without the rest of a leg's context. ---- *)
let WB_CASES_TAC x (lo,hi) side_tac =
  let disj = end_itlist (fun a b -> mk_disj(a,b))
     (map (fun k -> mk_eq(x, mk_small_numeral k)) (lo--hi)) in
  SUBGOAL_THEN disj MP_TAC THENL [side_tac; ALL_TAC] THEN STRIP_TAC;;

let BOUNDS_ARITH_TAC bnds =
  MAP_EVERY (MP_TAC o ASSUME) bnds THEN POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;;

(* ---- n-way concrete split of a bounded nblk leg (lo..hi), then close each band ---- *)
let split_close_tac lo hi =
  WB_CASES_TAC `nblk:num` (lo,hi) ASM_ARITH_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  concrete_band_close_tac;;

(* ---- reusable safety back-legs, starting at the compare just before the
   correctness proof's q_at seam.  At pc+0xbcc X5 is the public residual byte
   count; the theorem executes the compare and the initial ciphertext/H^8 loads
   itself, so its interface does not need to carry condition-code assumptions.
   From here the trace depends only on the public addresses and the fixed
   residual block count; all SIMD/data values may remain unconstrained.

   Prove each residual tail ONCE against the caller's whole-buffer bounds.  The
   selected witnesses below are closed choice terms, so all three consumers
   (5..8, 9..16, and >=17) can reuse them without existential-witness escape. ---- *)
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
   WB_SAFETY_BYTES_LEN matches `val (word (128*nblk)) DIV 8 * 1`, but by the time
   the >=17 residue reaches its events discharge the goal's bound is already spelled
   `(128 * nblk) DIV 8 * 1`: CORE_SAFE_OPEN_TAC asserts `val (word (128*nblk)) =
   128*nblk` into the assumptions, and WB_TAIL_POST_ASM_REWRITE_TAC (which rewrites
   with every `val`-headed assumption) consumes the `val (word ...)` wrapper on the
   goal side.  The assumption side, stripped straight off the reusable tail theorem,
   keeps the val spelling.  So WB_SAFETY_BYTES_LEN cannot fire on the goal, and
   the two sides end up as `(128*nblk) DIV 8 * 1` and `16*nblk`.
   This rule closes that gap.  It needs no size side-condition: with the word
   wrapper already gone it is pure natural-number arithmetic, which is also why it is
   safe to keep unconditionally in the rewrite set.  The 9..16 bands never need it
   (nblk is a numeral there, so NUM_REDUCE collapses the bound outright). *)
let WB_SAFETY_BYTES_LEN_NOVAL = prove
 (`!nblk. (128 * nblk) DIV 8 * 1 = 16 * nblk`,
  GEN_TAC THEN
  MP_TAC(SPECL [`8`; `16 * nblk`] DIV_MULT) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* memaccess_inbounds distributes over a loop trace: if every iteration's own
   trace is in bounds, so is the concatenation ENUMERATEL builds.  Needed on the
   >=17 leg only, whose scaffold keeps the loop body symbolic in `i` -- the
   bands 1..16 unroll to concrete traces and never produce an ENUMERATEL goal.
   Stock consttime.ml has MEMACCESS_INBOUNDS_APPEND/_CONS/_MEM but no ENUMERATEL
   rule, so a quantified loop trace matches none of its dispatch cases. *)
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
   replaced by meminb_tac -- the shape of the shared DISCHARGE_SAFE_ROBUST. *)
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
          (word pc,LENGTH aes128_gcm_dec_alt_tmc) (stackpointer,80) /\
        ALLPAIRS nonoverlapping
          [out_p,16 * nblk; xi_p,16; ivec_p,16]
          [word pc,LENGTH aes128_gcm_dec_alt_tmc]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
                  read PC s = word (pc + 0xbcc) /\
                  read X0 s = tail_in /\
                  read X2 s = tail_out /\
                  read X3 s = xi_p /\
                  read X5 s = word (16 * rr) /\
                  read X6 s = htbl_p /\
                  read X10 s = word_add stackpointer (word 64) /\
                  read X16 s = ivec_p /\
                  read events s = e)
             (\s. read PC s = word (pc + 3756) /\
                  (exists e2.
                       read events s = APPEND e2 e /\
                       e2 =
                       f_events in_p key_p htbl_p out_p xi_p ivec_p nblk
                                tail_in tail_out pc stackpointer /\
                       memaccess_inbounds e2
                       [in_p,16 * nblk; xi_p,16; ivec_p,16;
                        key_p,176; htbl_p,192; out_p,16 * nblk;
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
      `nonoverlapping (word pc,5008) (tail_out:int64,tail_len)` in
  let tail_reads =
    subst [tail_len,`tail_len:num`]
      `[(tail_in:int64),tail_len; xi_p,16; ivec_p,16; key_p,176; htbl_p,192;
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
     [`nonoverlapping (word pc,5008) (out_p:int64,16 * nblk)`;
      `nonoverlapping (word pc,5008) (xi_p:int64,16)`;
      `nonoverlapping (word pc,5008) (ivec_p:int64,16)`] THEN
    SUBGOAL_THEN tail_code_nonoverlap ASSUME_TAC THENL
     [MATCH_MP_TAC NONOVERLAPPING_SUBREGIONS THEN
      MAP_EVERY EXISTS_TAC
       [`word pc:int64`; `5008`; `out_p:int64`; `16 * nblk`] THEN
      ASM_REWRITE_TAC[WB_CONTAINED_REFL];
      ALL_TAC] THEN
    SUBGOAL_THEN
      `val (word (128 * nblk):int64) DIV 8 * 1 = 16 * nblk`
      SUBST_ALL_TAC THENL
     [MATCH_MP_TAC WB_SAFETY_BYTES_LEN THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    DRIVE_TAC 3756 400 THEN
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

(* The accumulated event trace of state st: the RHS of its `read events st`
   assumption. *)
let events_of_state asl st =
  rhs(concl(snd(find (fun (_,th) ->
    let c = concl th in
    is_eq c &&
    (try rator(lhs c) = `read events` && rand(lhs c) = st with _ -> false))
    asl)));;

(* Specialize the selected r-block tail theorem to a leg with block count nblk
   whose residual tail reads tail_in and writes tail_out, at the current
   accumulated event trace of state sname.  Using the state equation's RHS keeps
   the old state variable from surviving ARM_BIGSTEP_TAC's cleanup. *)
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

   COMPOSE_FRAME_LEMMA is split out so MESON only ever sees the frame
   composition.  Handing it the whole composed statement instead diverges: the
   `seq` existential multiplies with `eventually`'s own quantifier. *)
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
   tail's own ensures, which is then the tail theorem, followed by its frame and,
   by post_tac, the enclosing postcondition. *)
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
    (* On legs whose tail is entered after a long symbolic front, the front
       leaves the leftover-byte count in X5 as the unreduced difference
       `word_sub (in_p + 16*nblk) (in_p + 128*k)`, so the blanket rewrite
       closes 9 of the 10 precondition conjuncts and leaves one word
       equation.  WORD_RULE finishes it.  The 5..8 legs enter the tail at s0,
       where every conjunct is literally an assumption and nothing is left --
       hence TRY, which keeps the step available without being load-bearing. *)
    BETA_TAC THEN ASM_REWRITE_TAC[] THEN TRY(CONV_TAC WORD_RULE)];;

(* ---- net-safe rewriting for the composed tails.  On the 9..16 and >=17 legs,
   which reach their tail after a long symbolic front, the assumption list carries
   that front's per-state reads plus front_916_setup_tac's asserted USHR /
   AND-mask / DIVISION identities, among which are cyclic equation pairs.  A
   rewrite *net* (REWRITE_TAC, ASM_SIMP_TAC, any TOP_DEPTH traversal) re-descends
   into its own output and diverges on such a pair, overflowing the stack
   ("looping recursion?"); narrowing the assumption set alone does not prevent
   it.  A single ONCE_DEPTH pass rewrites every redex at most once and cannot
   cycle, so WB_BOUNDED_REWRITE_CONV ths k repeats such passes only while the
   term keeps changing, and at most k times.

   wb_tail_rewrite_asms selects the assumptions a composed tail's goal can use.
   That goal mentions only the freshly generalized final state and the event
   list, so only three kinds of assumption can contribute: variable definitions
   (the stripped `e2 = f_events ...`), reads of a state the goal still mentions,
   and the `val (word ...)` size facts the enclosing spec's buffer bounds are
   phrased over.  The rest are dropped rather than discharged. ---- *)
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

(* Targeted stand-in for the blanket ASM_REWRITE_TAC[] at the head of a composed
   tail's post-tactic, which overflows on the 9..16 and >=17 legs (unlike the 5..8
   legs, whose tail starts at s0); ASM_SIMP_TAC is no better, having the same
   assumption set and the same net.  The trailing REWRITE_TAC[] closes the trivial
   conjuncts a blanket call would. *)
let WB_TAIL_POST_ASM_REWRITE_TAC : tactic = fun (asl,w) ->
  (CONV_TAC (WB_BOUNDED_REWRITE_CONV (wb_tail_rewrite_asms (asl,w)) 12) THEN
   REWRITE_TAC[]) (asl,w);;

(* After MEMACCESS_INBOUNDS_APPEND splits the trace, the first conjunct is the
   reusable tail theorem's own `memaccess_inbounds` postcondition, which is already
   an assumption -- so it needs matching, not search.  A blanket ASM_MESON_TAC[] is
   handed all 64 assumptions instead and diverges on the 9..16 and >=17 legs.  Trying
   the two assumption-matching tactics first closes that case immediately and never
   reaches MESON.

   The fallback must be the *unrestricted* ASM_MESON_TAC[].  Restricted to the
   inbounds assumptions it fails on band 5 with `solve_goal: Too deep`: the 5..8 legs
   reach this conjunct in a shape that genuinely needs facts beyond the inbounds
   ones.

   Plain matching is still not enough on the 9..16 and >=17 legs, because the two
   sides spell the same buffer bound differently.  mk_tail_safe_goal states the tail's
   postcondition over `val (word (128 * nblk):int64) DIV 8 * 1`, and prove_tail_safe
   SUBST_ALL_TACs that to `16 * nblk` only *inside* its own proof, so the exported
   theorem keeps the `val` spelling.  The enclosing band closers then run
   `RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV)` and `CONV_TAC NUM_REDUCE_CONV` over a
   leg where nblk is already a numeral, which collapses one side to a literal (`144`
   at band 9) while the other keeps the `val (word ...) DIV 8 * 1` form.  The 5..8
   legs never diverge this way because they specialize the tail at s0 with no
   intervening reduction.  So normalize both sides to the same spelling and try the
   match again; equality-shaped goals and the legs the plain matches close are
   untouched, because the plain matches are tried first.

   The decisive normalizer is APPEND_NIL.  Both sides carry the tail's selector
   `(@f_events. ...) in_p key_p ... stackpointer` -- the goal's copy inside a
   `memaccess_inbounds` argument, the assumption's as the `e2 = ...` definition.  But
   RESHAPE_LOOP_TAC leaves the goal's copy with `APPEND (APPEND [...] []) []`
   wrappers around the range lists *inside the epsilon's body*, where the
   assumption's copy has the bare lists.  Two epsilon terms whose bodies differ at
   all are different terms, so `e2` never rewrites and the conjunct cannot match
   however the bounds are spelled.  APPEND_NIL collapses the wrappers and the two
   selectors become alpha-equal.

   WB_SAFETY_BYTES_LEN and the `val` size facts additionally reconcile the buffer
   bounds, spelled `val (word 1152) DIV 8 * 1` in the
   assumption against the literal `144` in the goal.  WB_SAFETY_BYTES_LEN is the rule
   prove_tail_safe itself uses for this bound; it matters on the >=17 leg, where nblk
   stays symbolic and the `val` facts alone would leave `(128 * nblk) DIV 8 * 1`
   needing symbolic arithmetic that neither NUM_REDUCE nor MESON closes. *)
let WB_TAIL_EVENTS_DISCHARGE_TAC : tactic = fun (asl,w) ->
  let bytelen =
    mapfilter (fun (_,th) -> MATCH_MP WB_SAFETY_BYTES_LEN th) asl in
  let valfacts = map snd (filter (fun (_,th) ->
      let c = concl th in
      is_eq c &&
      (match strip_comb(lhs c) with
       | Const("val",_),_ -> true
       (* the stripped `e2 = f_events ...` definition.  Without it the assumption
          keeps the bare variable `e2` where the goal has the selector it stands for,
          so the two can never converge no matter how the rest is normalized. *)
       | _ -> is_var(lhs c))) asl) in
  (* WB_SAFETY_BYTES_LEN_NOVAL is unconditional, so it is prepended rather than
     derived from an assumption: on the >=17 leg the goal's bound has already lost its
     `val (word ...)` wrapper, so WB_SAFETY_BYTES_LEN cannot reach it.  See that
     lemma's own comment. *)
  let rules = WB_SAFETY_BYTES_LEN_NOVAL :: bytelen @ valfacts in
  (* APPEND_NIL gets TOP_DEPTH, because the wrappers are nested two deep
     (`APPEND (APPEND l []) []`) and a single ONCE_DEPTH pass strips only the outer
     one, leaving the two epsilon terms still unequal.  It is a terminating
     orientation (the RHS is a strict subterm), so a full traversal cannot cycle.

     The assumption-derived rules must NOT get TOP_DEPTH: it overflows on the
     cyclic-pair hazard described at WB_BOUNDED_REWRITE_CONV.  But a single
     ONCE_DEPTH pass is also not enough -- the bounds needing rewriting sit
     *inside* the epsilon's body, below the first redex the pass consumes, so goal
     and assumption normalize to shapes that still differ there -- hence the
     repeated passes of WB_BOUNDED_REWRITE_CONV. *)
  (* APPEND_NIL must run BOTH before and after the assumption-rule expansion.
     On the goal side the wrappers are present from the start, so the leading pass
     strips them.  On the assumption side they are not: there the trace is still the
     bare variable `e2`, and the wrappers only materialize once the `e2 = <selector>`
     definition has been rewritten in -- i.e. only after the leading pass has
     already run.  With the leading pass alone the two sides would therefore
     normalize to epsilon terms whose bodies differ by exactly
     `APPEND (APPEND [...] []) []`, and since epsilon terms with any difference in
     their bodies are different terms, the match could not fire however the bounds
     were spelled, and the goal would fall through to the diverging ASM_MESON_TAC[].
     With the trailing pass both sides become alpha-equal.  On the 5..8 and 9..16
     legs nblk is a numeral, so their bounds have already converged and the
     trailing pass leaves the stripped term unchanged.  Repeating the pass is safe
     for the reason the leading one is: APPEND_NIL's RHS is a strict subterm, so a
     full traversal terminates. *)
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

   The stock tactic stack-overflows with "looping recursion?" on the 9..16 and
   >=17 legs, which reach this conjunct with 63 assumptions.  Its one blanket
   call is the ASM_REWRITE_TAC[] inside
   DISCHARGE_MEMACCESS_INBOUNDS_USING_ASM_TAC, whose stated
   job is just to expand the stripped `e2 = f_events ...` definition so the
   undischarged assumption and the goal take the same shape.  It is the failure
   mode described at WB_BOUNDED_REWRITE_CONV, and the remedy is the same: bound
   the TRAVERSAL rather than narrow the fact set.  The overflow needs the cycle to
   be reachable from the goal.

   On the shapes the stock tactic does close -- identical-term match, range
   widening, concrete goal, and APPEND-split with and without `e2` defined -- the
   shadow agrees with it exactly, so the already-passing 5..8 legs keep their path.

   Everything here is the stock tactic transcribed verbatim apart from that one
   call and a recursion cap on main_tac, which turns a non-shrinking trace into a
   Failure the enclosing ORELSE can act on instead of an exhausted OCaml stack.

   The traversal is made of the same single ONCE_DEPTH passes as
   WB_BOUNDED_REWRITE_CONV, repeated because the shapes needing normalization sit
   below the first redex, inside the tail selector's epsilon body.  But here
   repetition stops when a term *repeats*, not merely when it stops changing: an
   oscillating equation pair flips the term's parity on every pass, so a
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

     (1) REPEAT CONJ_TAC.  main_tac dispatches on `memaccess_inbounds` heads and
     on MEMACCESS_INBOUNDS_APPEND, so a top-level `/\` matches nothing at all and
     the whole tactic reports "could not identify the pattern".  The >=17 leg
     gets one because its scaffold entry is APPEND residue (APPEND (ENUMERATEL
     ..) front): DISCHARGE_WB_COMPOSED_TAIL_TAC's REWRITE_TAC
     [MEMACCESS_INBOUNDS_APPEND] then distributes all the way down and hands this
     call a five-way conjunction.  Bands 9..16 enter the scaffold at a bare
     f_ev_k with no APPEND, so their goal stays a single mi term and REPEAT
     CONJ_TAC is a no-op there.

     (2) the ENUMERATEL rule.  Of those five conjuncts four are concrete traces
     that main_tac already closes; the fifth is the symbolic loop trace, and it
     needs the quantified-i step before the per-iteration body -- which main_tac
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


(* ---- the nblk 9..16 leg: symbolic front, then concretize per band.  A
   concrete-band DRIVE from s0 does NOT work here: the front branch at 0x340 is a
   flag compare rather than an affine word_sub, so the resolver cannot make its PC
   concrete.  Hence the front runs symbolically off WB_LOOPENTER_FLAGS_GE9 and each
   band is concretized only afterwards. ---- *)

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

(* front sim 1--229 -> pc+944 (0x3b0); resolve 0x3a8; step 230 -> pc+2044 (0x7fc) *)
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

(* ---- the nblk>=17 leg.  Its trace is already in ENSURES_EVENTS_WHILE_UP2 shape:
     e2 = APPEND <residue ladder> (APPEND (ENUMERATEL ((nblk-9) DIV 8) f_ev_loop)
                                          f_ev_front)
   so the residue ladder lands in the rule's discarded e_back.  The scaffold below
   gives the ladder its eight residue metavars, one per (nblk-9) MOD 8 value, since
   HOL metavars are shared across the goalstack and a single shared one would be
   fixed by whichever residue closed first. ---- *)

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

(* ---- >=17 entry prep: establish the bounds and collapse the 16-way ladder to its
   else-branch.  Collapsing it by asserting sixteen `~(nblk = k)` hypotheses instead is
   ruinously slow: those hypotheses are walked once per simulation step and again by
   DISCHARGE_SAFETY_PROPERTY_TAC over the whole trace, which turns seconds into tens of
   minutes.  Hence the rewrite carries the already-present 17<=nblk and leaves no
   hypotheses behind. ---- *)
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

(* ---- RESHAPE the collapsed trace for SEQUENCE:
        APPEND ladder (APPEND loop front) -> APPEND (APPEND ladder (APPEND loop [])) front
   so SEQUENCE at the loop head peels e_front_tail = front, e_back = APPEND ladder (APPEND loop []).
   NOTE: must use ONCE_REWRITE_TAC (GEN_REWRITE_TAC with a RAND o ONCE_DEPTH path silently
   missed the intended APPEND occurrence). ---- *)
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
     read X6 s = htbl_p /\
     read X3 s = xi_p /\
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
     read X3 s = xi_p /\
     read X4 s = word_add in_p (word (16 * nblk)) /\
     read X5 s = word (16 * nblk) /\
     read X6 s = htbl_p /\
     read X9 s = word (16 * nblk) /\
     read X10 s = word_add stackpointer (word 64) /\
     read X11 s = key_p /\
     read X16 s = ivec_p`;;

(* Collapse the first four concrete leaves of core_scaffold and expose the
   APPEND shared by the 5..8 band without first concretizing nblk. *)
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
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xbcc` front_58_inv THEN CONJ_TAC;;

(* ---- the and-mask on the 5..8 front: 16 * nblk - 1 rounded down to a
   multiple of 128 is 0 for 1 <= nblk <= 8 (the correctness proof states it
   for any nblk as AND_MASK_16NBLK_ANY). ---- *)
let AND_MASK_16NBLK = prove
 (`!nblk. 1 <= nblk /\ nblk <= 8
        ==> word_and (word_sub (word (16 * nblk)) (word 1))
                     (word 18446744073709551488):int64 = word 0`,
  GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `1 <= n /\ n <= 8 <=>
    n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV);;

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

(* ---- >=17 leg entry.  Leaves two subgoals: the front (pc+28 -> pc+948), then the
   rest (loop + tail, pc+948 -> pc+3756). ---- *)
let GE17_ENTER_TAC =
  GE17_PREP_TAC THEN RESHAPE_LOOP_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x3b4` front_inv THEN CONJ_TAC;;

(* ---- the >=17 front leg, pc+28 -> pc+948 (the loop head).  The branch at 0x3b0
   is the loop-entry compare, resolved off WB_PTRCMP_FLAGS and D_GT_128 rather than by
   the affine resolver, since both of its operands are symbolic in nblk. ---- *)
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

(* ---- loop invariant: the register state at the loop head on iteration i.  WHILE
   augments it with e2 = APPEND (ENUMERATEL i f_ev_loop) (APPEND [] front). ---- *)
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
     read X6 s = htbl_p /\
     read X3 s = xi_p /\
     read X11 s = key_p`;;

(* ---- LOOP decomposition: on the rest subgoal (prePC=pc+948) after GE17 front closed.
        ENSURES_EVENTS_WHILE_UP2_TAC then REPEAT CONJ_TAC yields 4 subgoals in ORDER:
          G0 count-nonzero ~((nblk-9)DIV8=0)
          G1 entry (i=0)         prePC=pc+948 (establish inv at 0)
          G2 loop BODY (forall i) -- the crux
          G3 exit/TAIL           prePC=pc+2044 -> pc+3756 (residue dispatch)   ---- *)
let GE17_LOOP_OPEN_TAC =
  ENSURES_EVENTS_WHILE_UP2_TAC `(nblk - 9) DIV 8` `pc + 0x3b4` `pc + 0x7fc` loop_inv THEN
  REPEAT CONJ_TAC;;

(* G0 count-nonzero *)
let GE17_COUNT_TAC =
  MP_TAC(ASSUME `17 <= nblk`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  SIMP_TAC[DIV_EQ_0; ARITH_EQ] THEN ARITH_TAC;;

(* G1 entry (i=0): precond=postcond after normalizing 0+1, 128*1, ENUMERATEL 0, APPEND [], *1 *)
let GE17_ENTRY_TAC =
  ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[ENUMERATEL; APPEND; ADD_CLAUSES; MULT_CLAUSES] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_exists (concl th))) THEN
  ASM_REWRITE_TAC[MULT_CLAUSES];;

(* G2, the loop body.  STRIP_EXISTS_ASSUM_TAC after ENSURES_INIT_TAC is required, not
   cosmetic: the invariant carries an accumulated `exists e2. read events s0 = APPEND e2 e
   /\ ...`, and unless it is stripped, `read events s0` is never exposed and the closing
   EXISTS_E2_TAC fails in AP_THM_TAC.  This mirrors what
   bignum_copy_row_from_table_8n.ml gets from ARM_SIM_TAC's
   ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC).  WBN_PC_BRIDGE already has i free, so it
   is MP'd rather than SPEC'd. *)
let ptrcmp_i = SPECL [`in_p:int64`; `128 * (i + 2)`; `128 * ((nblk - 1) DIV 8)`] WB_PTRCMP_FLAGS;;
let x0norm_i = WORD_RULE
  `word_add (word_add in_p (word (128 * (i + 1)))) (word 128):int64 = word_add in_p (word (128 * (i + 2)))`;;
let pcbridge_i = MP WBN_PC_BRIDGE (ASSUME `9 <= nblk`);;

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

(* ---- G3, the exit/tail leg, pc+2044 -> pc+3756: a straight-line prepretail to
   pc+3020, then the 8-way dispatch on the leftover block count (nblk-9) MOD 8. ---- *)

(* the leftover-byte count left in X5 at pc+3020, guarded by 17<=nblk + no overflow. *)
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

(* tail setup: init, strip the accumulated e2, and simulate only the shared
   prepretail prefix to the tail compare at pc+0xbcc. *)
let GE17_TAIL_SETUP_TAC =
  LEG_INIT_TAC THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_QSTEPS_TAC EXEC (1--244) THEN                (* pc+2044 -> pc+3020 *)
  MP_TAC TAIL_LEFTOVER_BYTES THEN ANTS_TAC THENL
   [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  SUBGOAL_THEN `(nblk - 9) MOD 8 < 8` ASSUME_TAC THENL
   [MP_TAC(SPECL [`nblk - 9`; `8`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN ARITH_TAC; ALL_TAC];;

(* per-residue closer: drive the concrete residue tail to pc+3756, collapse the ladder
   down to this residue's f_ev_t<rr>, then discharge. *)
let close_tail_residue rr =
  (* the DIVISION identity is load-bearing: without it CONTAINED_TAC's arithmetic
     cannot show the residue store at out_p+128*((nblk-9) DIV 8+1)+k is in bounds. *)
  SUBGOAL_THEN `16 * nblk = 128 * ((nblk - 9) DIV 8 + 1) + 16 * ((nblk - 9) MOD 8 + 1)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`nblk - 9`; `8`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
    MP_TAC(ASSUME `17 <= nblk`) THEN ARITH_TAC; ALL_TAC] THEN
  MP_WB_TAIL_SAFE_TAC (rr+1) "s244" `nblk:num`
    `word_add in_p (word (128 * ((nblk - 9) DIV 8 + 1))):int64`
    `word_add out_p (word (128 * ((nblk - 9) DIV 8 + 1))):int64` THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALLPAIRS; ALL; WB_MC_LEN] THEN
    REPEAT CONJ_TAC THEN
    (* This leg's antecedent needs two alternatives the 9..16 bands do not,
       because here nblk is still symbolic: three of the eight conjuncts are not
       discharged by the assumption hit.

       (a) `1 <= nblk` follows from the leg's `17 <= nblk`, so it needs an
       arithmetic closer.  It must be NBLK_ARITH_TAC, not ASM_ARITH_TAC: at this
       point the goal carries the ~60 post-simulation memory assumptions, and
       handing those to the arithmetic decision procedure exhausts memory.
       NBLK_ARITH_TAC keeps only the two nblk bounds and drops the rest before
       ARITH_TAC.

       (b) the two `contained (tail_ptr,16*(rr+1)) (base,16*nblk)` conjuncts need
       `contained` unfolded first: CONTAINED_TAC (common/components.ml)
       leads with GEN_REWRITE_TAC I [GSYM CONTAINED_MODULO_MOD2] and so only
       applies to a top-level contained_modulo -- on a folded `contained` it
       *raises* REWRITES_CONV rather than failing (of the rewrite tactics only
       the `I` traversal raises on a no-match).  The
       DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC that prove_tail_safe above
       uses does the same REWRITE_TAC[contained] before its contained closer.

       As in the 9..16 chain below, MUST makes every alternative close its
       conjunct or fail.  Unlike that chain there is no NUM_REDUCE step: nblk is
       symbolic, so it would close none of these conjuncts. *)
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

(* per-band closer for nblk 9..16, concretizing off the shared symbolic front. *)
let close_916_band k =
  let r = k - 8 in
  let structural_closers =
    [REWRITE_TAC[contained] THEN CONTAINED_TAC; CONTAINED_TAC;
     WB_FIRST_NONOVERLAPPING_TAC] in
  UNDISCH_TAC (mk_eq(`nblk:num`, mk_small_numeral k)) THEN DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  (* s474: the shared front walks all the way to the tail theorem's entry
     pc+3020, the 230 front steps and the 244 prepretail and tail-entry steps.
     Not s477 -- by then the ldr q9,[x0],#16 has advanced X0 to in_p+144, so
     the eight precondition registers are simultaneously correct only at
     s474. *)
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
       a structural conjunct whose numerals are still unfolded (`nonoverlapping
       (out_p,16 * 9) ...`) it only normalizes the spelling, so the structural
       closers are retried after it.  TRY keeps the arithmetic case, where the
       retry has nothing left to do. *)
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
    (* WORD_RULE normalizes the tail's pointer arithmetic when any survives, but
       on these bands the preceding NUM_REDUCE already leaves the goal as the
       event-trace existential, which is not a word equation -- WORD_RULE then
       dies in RAND_CONV.  The 5..8 closer omits the step entirely for the same
       reason; TRY keeps it available without making it load-bearing. *)
    TRY(CONV_TAC WORD_RULE) THEN
    DISCHARGE_WB_COMPOSED_TAIL_TAC);;

(* ---- the core safety opening.  Unlike a `\s s'. true` frame, this one unfolds
   MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI up front so ENSURES_FINAL_STATE_TAC can
   discharge the real frame at every leaf; the wrapper needs the real frame, because it
   simulates the epilogue after the core big-step and so needs aligned_bytes_loaded
   preserved across it.  Mirrors BIGNUM_INV_P25519_SAFE. ---- *)
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

(* ---- the ABI wrapper.  Stock ARM_ADD_RETURN_STACK_TAC does not apply: the exported
   spec quantifies over the C argument bit_len, while the core below takes
   word (128 * nblk) with 1 <= nblk, and the prologue contains the entry guard, whose
   zero and non-multiple-of-128 branches return before the core.  The crossing is
   therefore hand-rolled, mirroring the functional wrapper WBN_DEC_SUBROUTINE_BYTELIST
   above. ---- *)

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

(* ---- the core safety theorem, over the real MAYCHANGE frame the wrapper needs.
   Its memaccess bounds are the assembly's exact footprint.  The public theorem
   below takes its bounds from the C signature through mk_safety_spec: the tag and
   ivec (16), key (176) and htable (192) bounds and the 80-byte frame equal this
   footprint, while the in/out bounds are the C length len_bits/8 (val bit_len DIV 8
   bytes), which contains the 16 * nblk footprint and equals it when
   bit_len = word (128 * nblk). ---- *)
let AES128_GCM_DEC_ALT_SAFE = prove
 (`exists f_events.
     forall e pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p nblk.
         1 <= nblk /\
         128 * nblk < 2 EXP 64 /\
         val in_p + 16 * nblk < 2 EXP 63 /\
         aligned 16 stackpointer /\
         ALLPAIRS nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16]
         [word pc,LENGTH aes128_gcm_dec_alt_tmc; in_p,16 * nblk;
          key_p,176; htbl_p,192; stackpointer,80] /\
         PAIRWISE nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16] /\
         ALL (nonoverlapping (stackpointer,80))
         [word pc,LENGTH aes128_gcm_dec_alt_tmc; in_p,16 * nblk;
          key_p,176; htbl_p,192]
         ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_alt_tmc /\
                  read PC s = word (pc + 28) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS
                  [in_p; word (128 * nblk); out_p; xi_p; ivec_p; key_p; htbl_p]
                  s /\
                  read events s = e)
             (\s. read PC s = word (pc + 3756) /\
                  (exists e2.
                       read events s = APPEND e2 e /\
                       e2 =
                       f_events in_p key_p htbl_p out_p xi_p ivec_p nblk pc
                       stackpointer /\
                       memaccess_inbounds e2
                       [in_p,16 * nblk; xi_p,16; ivec_p,16;
                        key_p,176; htbl_p,192; out_p,16 * nblk;
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
   CONCRETIZE + UNIFY_REFL.  The latter leaves the core's X_CHOOSE'd
   f_events_callee variable in the witness, which then escapes its scope and
   makes the CHOOSE fail at extraction.

   The public witness dispatches only on public bit_len:
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
         [EventJump (word (pc + 3784),ra);
          EventJump (word pc,word (pc + 3780))]
       else
         APPEND
           [EventJump (word (pc + 3776),ra); EventLoad (sp,16);
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
       [EventJump (word (pc + 3784),ra);
        EventJump (word (pc + 8),word (pc + 3780));
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
    (assoc "aes128_gcm_dec_alt" subroutine_signatures)
    AES128_GCM_DEC_ALT_NOIBT_SUBROUTINE_CORRECT
    AES128_GCM_DEC_ALT_EXEC;;

(* The statement of the exported safety theorem, for an arbitrary bit_len,
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
     forall e pc stackpointer in_p bit_len out_p xi_p ivec_p key_p htbl_p
            returnaddress.
         val in_p + 16 * gcm_wb_blocks bit_len < 2 EXP 63 /\
         aligned 16 stackpointer /\
         ALLPAIRS nonoverlapping
         [out_p,16 * gcm_wb_blocks bit_len; xi_p,16; ivec_p,16]
         [word pc,LENGTH aes128_gcm_dec_alt_tmc;
          in_p,16 * gcm_wb_blocks bit_len; key_p,176; htbl_p,192;
          word_sub stackpointer (word 80),80] /\
         PAIRWISE nonoverlapping
         [out_p,16 * gcm_wb_blocks bit_len; xi_p,16; ivec_p,16] /\
         ALL (nonoverlapping (word_sub stackpointer (word 80),80))
         [word pc,LENGTH aes128_gcm_dec_alt_tmc;
          in_p,16 * gcm_wb_blocks bit_len; key_p,176; htbl_p,192]
         ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    aes128_gcm_dec_alt_tmc /\
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
                        key_p,176; htbl_p,192; out_p,val bit_len DIV 8 * 1;
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
     forall e pc stackpointer in_p bit_len out_p xi_p ivec_p key_p htbl_p
            returnaddress.
         val in_p + 16 * gcm_wb_blocks bit_len < 2 EXP 63 /\
         aligned 16 stackpointer /\
         ALLPAIRS nonoverlapping
         [out_p,16 * gcm_wb_blocks bit_len; xi_p,16; ivec_p,16]
         [word pc,LENGTH aes128_gcm_dec_alt_mc;
          in_p,16 * gcm_wb_blocks bit_len; key_p,176; htbl_p,192;
          word_sub stackpointer (word 80),80] /\
         PAIRWISE nonoverlapping
         [out_p,16 * gcm_wb_blocks bit_len; xi_p,16; ivec_p,16] /\
         ALL (nonoverlapping (word_sub stackpointer (word 80),80))
         [word pc,LENGTH aes128_gcm_dec_alt_mc;
          in_p,16 * gcm_wb_blocks bit_len; key_p,176; htbl_p,192]
         ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    aes128_gcm_dec_alt_mc /\
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
                        key_p,176; htbl_p,192; out_p,val bit_len DIV 8 * 1;
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
    aes128_gcm_dec_alt_mc aes128_gcm_dec_alt_tmc
    AES128_GCM_DEC_ALT_NOIBT_SUBROUTINE_SAFE));;
