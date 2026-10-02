(* ============================================================================
   FAST, REUSABLE GMULTn builder for the AES-GCM decrypt band proofs.

   `build_GMULTn_fast n` returns a pair (PACKn_ID, GMULTn_FULL_CORRECT_BA):
     - PACKn_ID                : decN_tL  =  XOR_k (word_pmul a_k b_k)   (256-bit)
     - GMULTn_FULL_CORRECT_BA  : polyval_reduce_prop3 (XOR_k word_pmul a_k b_k)
                                 expressed in the machine's Karatsuba-limb byteform.

   This replaces the old hand-written `decN_tL` term + monolithic `CONV_TAC WORD_RULE`
   `PACKn_ID` (which bit-blasts a 256-bit identity and cost ~30s at N=2, ~373s at N=3,
   and never finished at N=4).  Method: prove `decN_tL = XOR_k dec1[k]` STRUCTURALLY
   by XOR-AC over opaque pmul atoms (`AC WORD_XOR_ACI`, no bit-blast), then fold each
   single-block `dec1[k]` to `word_pmul a_k b_k` via PMUL_KARATSUBA (0.02s each).  The
   whole build is ~0.1-0.4s for any N and is the shared GHASH-bridge multiply lemma for
   every dec band (le2/le3/le4 ... le8).

   Verified: build_GMULTn_fast 2 / 3 reproduce the old hand-written
   GMULT2_FULL_CORRECT_BA / GMULT3_FULL_CORRECT_BA concl EXACTLY.

   SELF-CONTAINED: needs only the common nblock GHASH layer (PMUL_KARATSUBA /
   KARATSUBA_LIMBS from common/ghash_nblock_karatsuba.ml); the shared Prop3
   reduction lemma GMULT_REDUCE_PROP3 (+ its V0LO helper) is proved HERE so the
   file loads correctly in ANY order.  (It was previously proved only inside
   the dec proof chain, which armed a load-order landmine: loading this file
   first failed with Unbound GMULT_REDUCE_PROP3, `needs` still marked it
   loaded, and the eventual caller died with Unbound build_GMULTn_fast.)
   ============================================================================ *)

needs "common/ghash_nblock_karatsuba.ml";;

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
let mk_packed_L n =
  let term k = let a=mk_var(Printf.sprintf "a%d" k,`:int128`) and b=mk_var(Printf.sprintf "b%d" k,`:int128`) in
               mk_comb(mk_comb(`word_pmul:int128->int128->256 word`,a),b) in
  match map term (0--(n-1)) with
  | x::rest -> List.fold_left (fun acc y -> mk_comb(mk_comb(`word_xor:256 word->256 word->256 word`,acc),y)) x rest
  | [] -> failwith "";;
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
