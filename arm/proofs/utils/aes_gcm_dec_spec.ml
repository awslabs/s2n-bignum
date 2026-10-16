(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* AES-256-GCM DECRYPT: whole-block output + GHASH specification.            *)
(*                                                                           *)
(* The 8x decrypt kernel (aesv8_gcm_8x_dec_256_wb) processes whole 16-byte   *)
(* blocks only, so these specs read the input byte buffer `x` as its         *)
(* len DIV 16 whole blocks, and the proof uses them only at len = 16 * N,    *)
(* N >= 1. Each band's readable wrapper states its postcondition as          *)
(* `gcm_dec_pt_bytes (16 * N) x ctr0 keys` (output) and                      *)
(* `gcm_dec_final_xi (16 * N) x xi h` (tag), with the block decomposition    *)
(* hidden. The per-N unfold lemmas GCM_DEC_GHASH_BLOCKS_WHOLE_N and          *)
(* GCM_DEC_PT_BYTES_WHOLE_N (N = 1..8) rewrite these back to the explicit    *)
(* N-block list a band's body produces, so the wrappers stay sim-free.       *)
(*                                                                           *)
(* Decrypt differs from encrypt only in what GHASH reads: output block k is  *)
(* word_xor ciphertext_k keystream_k (aes_ctr in aes_ctr_spec.ml), while     *)
(* GHASH runs over the raw ciphertext blocks                                 *)
(* `bytes_to_int128 (SUB_LIST (16*k,16) x)`, not over the plaintext.         *)
(*                                                                           *)
(* Vocabulary matches the binary's band theorems: base counter `ctr0`        *)
(* (= ivec), `aes256_encrypt` + `gcm_ctr_inc_iter`, GHASH key                *)
(* `byteswap128 h`, and `word_bytereverse` per block                         *)
(* (= word_reversefields 8, provably equal).                                 *)
(*                                                                           *)
(* Needs aes_ctr_spec.ml for aes_ctr_bytes and bytes_to_int128.              *)
(* ========================================================================= *)

needs "arm/proofs/utils/aes_ctr_spec.ml";;

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
   Output plaintext byte buffer (decrypt): counter mode over the same whole
   input blocks (aes_ctr XORs the keystream onto the ciphertext, recovering
   the plaintext).
   ---------------------------------------------------------------------------- *)
let gcm_dec_pt_bytes = new_definition
 `gcm_dec_pt_bytes (len:num) (x:byte list) (ctr0:int128) (keys:int128 list) : byte list =
    aes_ctr_bytes ctr0 (gcm_dec_blocks_from 0 (len DIV 16) x) keys`;;

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
