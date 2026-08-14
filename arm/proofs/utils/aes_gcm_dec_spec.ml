(* ============================================================================
   AES-256-GCM DECRYPT: recursive whole-buffer output + GHASH specification.

   This is the decrypt analogue of the encrypt spec layer (gcm_ct_rec /
   gcm_ghash_blocks / aes256_gcm_encrypt / gcm_final_xi).  It moves the
   per-block expansion OFF the readable band theorem statements and INTO recursive
   spec functions of the whole input byte buffer `x` and its length; each band's
   readable wrapper then states its postcondition as `gcm_dec_pt_bytes (val len) x
   ctr0 keys` (output) and `gcm_dec_final_xi (val len) x xi h` (tag), with the block
   decomposition hidden.  Per-N unfold lemmas (GCM_DEC_GHASH_BLOCKS_N /
   GCM_DEC_PT_BYTES_N) rewrite these back to the explicit N-block list a band's
   BODY produces, so the wrappers stay sim-free.

   The decrypt mirror of encrypt (XOR is symmetric):
     - plaintext output block k = word_xor (ciphertext block k) keystream_k
       (identical formula to enc's ciphertext store) — captured by our existing
       aes_ctr / aes_ctr_full_tail_bytes (arm/proofs/utils/aes_ctr_spec.ml).
     - GHASH is over the RAW ciphertext INPUT blocks (masked partial tail),
       NOT word_xor'd with the keystream — this is the one genuine dec/enc
       difference, so gcm_dec_ghash_blocks below uses the raw input blocks
       `bytes_to_int128 (SUB_LIST (16*k,16) x)` (enc GHASHes gcm_ct_rec instead).

   Vocabulary matches our binary's band theorems: base counter `ctr0` (= ivec),
   `aes256_encrypt` + `gcm_ctr_inc_iter` (our gcm_ctr_iter), GHASH key `byteswap128 h`,
   `word_bytereverse` per block (= word_reversefields 8, provably equal).

   needs arm/proofs/utils/aes_ctr_spec.ml (aes_ctr / aes_ctr_full_tail_bytes /
   int128_to_bytes / bytes_to_int128).
   ============================================================================ *)

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

(* Head-step: peel the first block (used by the per-N unfold lemmas). *)
let GCM_DEC_BLOCKS_FROM_STEP = prove
 (`!m i x. gcm_dec_blocks_from i (SUC m) x =
           CONS (bytes_to_int128 (SUB_LIST (16 * i, 16) x))
                (gcm_dec_blocks_from (i + 1) m x)`,
  REWRITE_TAC[gcm_dec_blocks_from]);;

(* Prefix of the (n+1)-block view is the n-block view; last element is block n.
   These two let the GHASH input spec thread the SAME whole (nfull+1)-block list
   `gcm_dec_blocks_from 0 (nfull+1) x` the output spec uses, then collapse back to
   the nfull-full-blocks ++ masked-block-n form the per-N unfold lemmas produce. *)
let SUBLIST_PREFIX_BLOCKS = prove
 (`!n i x. SUB_LIST (0,n) (gcm_dec_blocks_from i (n+1) x) = gcm_dec_blocks_from i n x`,
  INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[gcm_dec_blocks_from; ADD_CLAUSES; SUB_LIST_CLAUSES];
    REWRITE_TAC[ARITH_RULE `SUC n + 1 = SUC(n+1)`; gcm_dec_blocks_from; SUB_LIST_CLAUSES] THEN
    ASM_REWRITE_TAC[]]);;

let EL_LAST_BLOCKS = prove
 (`!n i x. EL n (gcm_dec_blocks_from i (n+1) x) =
           bytes_to_int128 (SUB_LIST (16 * (i + n), 16) x)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[ADD_CLAUSES; gcm_dec_blocks_from] THENL
   [REWRITE_TAC[ARITH_RULE `1 = SUC 0`; gcm_dec_blocks_from; EL; HD; ADD_CLAUSES];
    REWRITE_TAC[EL; TL] THEN ASM_REWRITE_TAC[ARITH_RULE `(i + 1) + n = SUC(i + n)`]]);;

(* ----------------------------------------------------------------------------
   GHASH input block list (decrypt), the RECURSIVE whole-buffer form, mirroring
   the output spec gcm_dec_pt_bytes: thread the SAME whole (nfull+1)-block view
   `gcm_dec_blocks_from 0 (nfull+1) x` (the output threads it through
   aes_ctr_full_tail_bytes) through the block-list tail-masker
   gcm_ghash_full_tail_blocks (nfull full blocks ++ masked block nfull), the GHASH
   analogue of aes_ctr_full_tail_bytes.  GHASHes the RAW input blocks (the one
   genuine dec/enc difference — enc GHASHes gcm_ct_rec).
   ---------------------------------------------------------------------------- *)
let gcm_ghash_full_tail_blocks = new_definition
 `gcm_ghash_full_tail_blocks (blks:int128 list) (nfull:num) (tail:num) : int128 list =
    APPEND (SUB_LIST (0,nfull) blks)
           [word_and (EL nfull blks) (word (2 EXP (8 * tail) - 1))]`;;

let gcm_dec_ghash_blocks = new_definition
 `gcm_dec_ghash_blocks (len:num) (x:byte list) : int128 list =
    let nfull = (len - 1) DIV 16 in
    let tail  = len - 16 * nfull in
    gcm_ghash_full_tail_blocks (gcm_dec_blocks_from 0 (nfull + 1) x) nfull tail`;;

(* The final GHASH accumulator Xi written to xi_p: byte-reverse in, run
   ghash_polyval_acc over the byte-reversed block list keyed by byteswap128 h,
   byte-reverse out.  (Matches the band BODY's xi_p postcondition exactly.) *)
let gcm_dec_final_xi = new_definition
 `gcm_dec_final_xi (len:num) (x:byte list) (xi:int128) (h:int128) : int128 =
    word_bytereverse
      (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
         (MAP word_bytereverse (gcm_dec_ghash_blocks len x)))`;;

(* ----------------------------------------------------------------------------
   Output plaintext byte buffer (decrypt): the recursive whole-buffer form.
   Reuses the proven aes_ctr_full_tail_bytes over the input-ciphertext block list
   (aes_ctr XORs the keystream, recovering the plaintext); nfull full plaintext
   blocks ++ the first `tail` bytes of the masked partial block.
   ---------------------------------------------------------------------------- *)
let gcm_dec_pt_bytes = new_definition
 `gcm_dec_pt_bytes (len:num) (x:byte list) (ctr0:int128) (keys:int128 list) : byte list =
    let nfull = (len - 1) DIV 16 in
    let tail  = len - 16 * nfull in
    aes_ctr_full_tail_bytes ctr0 (gcm_dec_blocks_from 0 (nfull + 1) x) keys nfull tail`;;

(* ----------------------------------------------------------------------------
   Arithmetic: for a CONCRETE nfull and 1 <= tail <= 16, discharge the two facts
   the unfold needs, with the EXACT term shape produced by let_CONV on the spec
   ( ((16*nfull+tail)-1) DIV 16 = nfull  and  (16*nfull+tail)-16*nfull = tail ).
   Built per concrete nfull so DIV reduces cleanly (no syntactic-match fragility).
   ---------------------------------------------------------------------------- *)
let gcm_dec_nfull_facts nfull =
  let n = mk_small_numeral nfull and ln = mk_small_numeral (16 * nfull) in
  (* divth: ((16*nfull + tail) - 1) DIV 16 = nfull, with 16*nfull a reduced numeral *)
  let divgoal = mk_imp(`1 <= tail /\ tail <= 16`,
    mk_eq(subst[ln,`L:num`] `((L + tail) - 1) DIV 16`, n)) in
  let divth = prove(divgoal,
    STRIP_TAC THEN
    (if nfull = 0 then MATCH_MP_TAC DIV_LT THEN ASM_ARITH_TAC
     else
      (SUBGOAL_THEN (subst[ln,`L:num`;n,`n:num`] `(L + tail) - 1 = n * 16 + (tail - 1)`) SUBST1_TAC THENL
        [ASM_ARITH_TAC; ALL_TAC] THEN
       SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN
       SUBGOAL_THEN `(tail - 1) DIV 16 = 0` SUBST1_TAC THENL
        [MATCH_MP_TAC DIV_LT THEN ASM_ARITH_TAC; ARITH_TAC]))) in
  (* subth: (16*nfull + tail) - 16*nfull = tail (both 16*nfull reduced numerals) *)
  let subgoal = mk_imp(`1 <= tail /\ tail <= 16`,
    mk_eq(subst[ln,`L:num`] `(L + tail) - L`, `tail:num`)) in
  let subth = prove(subgoal, ARITH_TAC) in
  (divth, subth);;

(* ----------------------------------------------------------------------------
   Per-N unfold lemmas (N = nfull+1 blocks: nfull full + 1 masked tail),
   mirroring the encrypt-side GHASH_BLOCKS_1..8.  These rewrite the whole-buffer
   spec back to the explicit block list a band's BODY produces, so the readable
   wrappers are proved by REWRITE + the existing sim-free bridges.  N=1..8 cover
   every band the routine has (more_than_1 .. more_than_7).
   ---------------------------------------------------------------------------- *)
(* Generic builder: prove the N-block unfold of gcm_dec_ghash_blocks (16*nfull+tail). *)
let build_ghash_blocks_lemma nfull =
  let lenb = mk_comb(mk_comb(`(+):num->num->num`, mk_small_numeral (16 * nfull)),`tail:num`) in
  let blk i = subst [mk_small_numeral (16 * i),`ofs:num`]
                `bytes_to_int128 (SUB_LIST (ofs, 16) (x:byte list))` in
  let mask t = mk_comb(mk_comb(`word_and:int128->int128->int128`,t),`word (2 EXP (8 * tail) - 1):int128`) in
  let elts = (map blk (0--(nfull-1))) @ [mask (blk nfull)] in
  let rhs = itlist (fun a b -> mk_comb(mk_comb(`CONS:int128->(int128)list->(int128)list`,a),b))
                   elts `[]:int128 list` in
  let goal = mk_forall(`tail:num`, mk_forall(`x:byte list`,
               mk_imp(`1 <= tail /\ tail <= 16`,
                 mk_eq(mk_comb(mk_comb(`gcm_dec_ghash_blocks`,lenb),`x:byte list`), rhs)))) in
  let divth, _ = gcm_dec_nfull_facts nfull in
  let subrw = ARITH_RULE (subst [mk_small_numeral (16 * nfull),`L:num`] `(L + tail) - L = tail`) in
  prove(goal,
    REPEAT STRIP_TAC THEN REWRITE_TAC[gcm_dec_ghash_blocks] THEN
    CONV_TAC(LAND_CONV(DEPTH_CONV let_CONV)) THEN
    ASM_SIMP_TAC[divth] THEN
    (* thread the whole (nfull+1)-block view through the tail-masker, then collapse
       prefix -> nfull-block view and last elt -> block nfull (SUBLIST_PREFIX/EL_LAST). *)
    REWRITE_TAC[gcm_ghash_full_tail_blocks; SUBLIST_PREFIX_BLOCKS; EL_LAST_BLOCKS] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[subrw] THEN
    REWRITE_TAC(map num_CONV (map mk_small_numeral (rev (1--(if nfull = 0 then 1 else nfull))))) THEN
    REWRITE_TAC[gcm_dec_blocks_from; APPEND] THEN
    CONV_TAC NUM_REDUCE_CONV);;

let GCM_DEC_GHASH_BLOCKS_1 = build_ghash_blocks_lemma 0;;
let GCM_DEC_GHASH_BLOCKS_2 = build_ghash_blocks_lemma 1;;
let GCM_DEC_GHASH_BLOCKS_3 = build_ghash_blocks_lemma 2;;
let GCM_DEC_GHASH_BLOCKS_4 = build_ghash_blocks_lemma 3;;
let GCM_DEC_GHASH_BLOCKS_5 = build_ghash_blocks_lemma 4;;
let GCM_DEC_GHASH_BLOCKS_6 = build_ghash_blocks_lemma 5;;
let GCM_DEC_GHASH_BLOCKS_7 = build_ghash_blocks_lemma 6;;
let GCM_DEC_GHASH_BLOCKS_8 = build_ghash_blocks_lemma 7;;

(* The plaintext-output-bytes unfold: gcm_dec_pt_bytes (16*nfull+tail) x ctr0 keys
   = aes_ctr_full_tail_bytes ctr0 [nfull+1 explicit blocks] keys nfull tail. *)
let build_pt_bytes_lemma nfull =
  let lenb = mk_comb(mk_comb(`(+):num->num->num`, mk_small_numeral (16 * nfull)),`tail:num`) in
  let blk i = subst [mk_small_numeral (16 * i),`ofs:num`]
                `bytes_to_int128 (SUB_LIST (ofs, 16) (x:byte list))` in
  let elts = map blk (0--nfull) in
  let blist = itlist (fun a b -> mk_comb(mk_comb(`CONS:int128->(int128)list->(int128)list`,a),b))
                     elts `[]:int128 list` in
  let rhs = list_mk_comb(`aes_ctr_full_tail_bytes`,
              [`ctr0:int128`; blist; `keys:int128 list`; mk_small_numeral nfull; `tail:num`]) in
  let goal = list_mk_forall([`tail:num`;`x:byte list`;`ctr0:int128`;`keys:int128 list`],
               mk_imp(`1 <= tail /\ tail <= 16`,
                 mk_eq(list_mk_comb(`gcm_dec_pt_bytes`,[lenb;`x:byte list`;`ctr0:int128`;`keys:int128 list`]), rhs))) in
  let divth, _ = gcm_dec_nfull_facts nfull in
  let subrw = ARITH_RULE (subst [mk_small_numeral (16 * nfull),`L:num`] `(L + tail) - L = tail`) in
  prove(goal,
    REPEAT STRIP_TAC THEN REWRITE_TAC[gcm_dec_pt_bytes] THEN
    CONV_TAC(LAND_CONV(DEPTH_CONV let_CONV)) THEN
    ASM_SIMP_TAC[divth] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_ADD_CONV)) THEN
    REWRITE_TAC(map num_CONV (map mk_small_numeral (rev (1--(nfull+1))))) THEN
    REWRITE_TAC[gcm_dec_blocks_from] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[subrw]);;

let GCM_DEC_PT_BYTES_1 = build_pt_bytes_lemma 0;;
let GCM_DEC_PT_BYTES_2 = build_pt_bytes_lemma 1;;
let GCM_DEC_PT_BYTES_3 = build_pt_bytes_lemma 2;;
let GCM_DEC_PT_BYTES_4 = build_pt_bytes_lemma 3;;
let GCM_DEC_PT_BYTES_5 = build_pt_bytes_lemma 4;;
let GCM_DEC_PT_BYTES_6 = build_pt_bytes_lemma 5;;
let GCM_DEC_PT_BYTES_7 = build_pt_bytes_lemma 6;;
let GCM_DEC_PT_BYTES_8 = build_pt_bytes_lemma 7;;

(* ----------------------------------------------------------------------------
   WHOLE-BLOCK (len = 16*N) unfolds for the whole-blocks-only decrypt variant
   (aesv8_gcm_8x_dec_256_wb): specialize the per-N masked unfolds at tail = 16
   and collapse the all-ones mask, giving plain unmasked block lists / the plain
   whole-block aes_ctr_bytes output.  N = 1..8.
   ---------------------------------------------------------------------------- *)
let build_ghash_blocks_whole n =
  let base = el (n-1) [GCM_DEC_GHASH_BLOCKS_1;GCM_DEC_GHASH_BLOCKS_2;
                       GCM_DEC_GHASH_BLOCKS_3;GCM_DEC_GHASH_BLOCKS_4;
                       GCM_DEC_GHASH_BLOCKS_5;GCM_DEC_GHASH_BLOCKS_6;
                       GCM_DEC_GHASH_BLOCKS_7;GCM_DEC_GHASH_BLOCKS_8] in
  let th = MP (SPECL [`16`;`x:byte list`] base) (ARITH_RULE `1 <= 16 /\ 16 <= 16`) in
  let th = REWRITE_RULE[WORD_AND_ALLONES_128] th in
  GEN `x:byte list` (CONV_RULE (LAND_CONV(RATOR_CONV(RAND_CONV NUM_REDUCE_CONV))) th);;

let GCM_DEC_GHASH_BLOCKS_WHOLE_1 = build_ghash_blocks_whole 1;;
let GCM_DEC_GHASH_BLOCKS_WHOLE_2 = build_ghash_blocks_whole 2;;
let GCM_DEC_GHASH_BLOCKS_WHOLE_3 = build_ghash_blocks_whole 3;;
let GCM_DEC_GHASH_BLOCKS_WHOLE_4 = build_ghash_blocks_whole 4;;
let GCM_DEC_GHASH_BLOCKS_WHOLE_5 = build_ghash_blocks_whole 5;;
let GCM_DEC_GHASH_BLOCKS_WHOLE_6 = build_ghash_blocks_whole 6;;
let GCM_DEC_GHASH_BLOCKS_WHOLE_7 = build_ghash_blocks_whole 7;;
let GCM_DEC_GHASH_BLOCKS_WHOLE_8 = build_ghash_blocks_whole 8;;

let build_pt_bytes_whole n =
  let base = el (n-1) [GCM_DEC_PT_BYTES_1;GCM_DEC_PT_BYTES_2;GCM_DEC_PT_BYTES_3;
                       GCM_DEC_PT_BYTES_4;GCM_DEC_PT_BYTES_5;GCM_DEC_PT_BYTES_6;
                       GCM_DEC_PT_BYTES_7;GCM_DEC_PT_BYTES_8] in
  let th = MP (SPECL [`16`;`x:byte list`;`ctr0:int128`;`keys:int128 list`] base)
              (ARITH_RULE `1 <= 16 /\ 16 <= 16`) in
  let collapse = PART_MATCH (lhs o rand) AES_CTR_FULL_TAIL_BYTES_WHOLE (rand(concl th)) in
  let collapse = MP collapse
      (prove(lhand(concl collapse), REWRITE_TAC[LENGTH] THEN ARITH_TAC)) in
  let th = TRANS th collapse in
  GENL [`x:byte list`;`ctr0:int128`;`keys:int128 list`]
    (CONV_RULE (LAND_CONV(funpow 3 RATOR_CONV (RAND_CONV NUM_REDUCE_CONV))) th);;

let GCM_DEC_PT_BYTES_WHOLE_1 = build_pt_bytes_whole 1;;
let GCM_DEC_PT_BYTES_WHOLE_2 = build_pt_bytes_whole 2;;
let GCM_DEC_PT_BYTES_WHOLE_3 = build_pt_bytes_whole 3;;
let GCM_DEC_PT_BYTES_WHOLE_4 = build_pt_bytes_whole 4;;
let GCM_DEC_PT_BYTES_WHOLE_5 = build_pt_bytes_whole 5;;
let GCM_DEC_PT_BYTES_WHOLE_6 = build_pt_bytes_whole 6;;
let GCM_DEC_PT_BYTES_WHOLE_7 = build_pt_bytes_whole 7;;
let GCM_DEC_PT_BYTES_WHOLE_8 = build_pt_bytes_whole 8;;
