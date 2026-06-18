(* ========================================================================= *)
(* One-block GHASH / mask / cascade closers for the AES-256-GCM band proofs.  *)
(*                                                                           *)
(* Split out of the former gcm_branch_closers.ml; also carries the shared    *)
(* partial-block mask construction lemmas used by every band.                *)
(* Pure-algebra closers (no machine code, no symbolic simulation); shared    *)
(* by the standalone per-N proof and the single-binary band proof.           *)
(* ========================================================================= *)

needs "arm/proofs/utils/gcm_aesgcm_nblock_helpers.ml";;

(* ===== ONE-BLOCK: partial-block mask construction + GHASH closers ======== *)
(* ========================================================================= *)
(* PARTIAL-BLOCK MASK CONSTRUCTION                                            *)
(*                                                                           *)
(* For an input of byte_len bytes (1 <= byte_len <= 16), the routine builds a *)
(* 128-bit mask register in Q0 from byte_len via the sequence                 *)
(*   and x1,#127 ; sub #128 ; neg ; and #127 ; lsrv (all-ones >> n) ;         *)
(*   cmp #64 ; csel ; csel ; ins d0/d1.                                       *)
(* The lemma below shows that this register, in the exact ival/flag form the  *)
(* symbolic simulator produces, equals word (2^(8*byte_len) - 1): a mask with *)
(* the low 8*byte_len bits set.  The proof peels byte_len into its 16 values  *)
(* (a single 16-way ARITH_RULE disjunction is intractable) and reduces each   *)
(* concrete case by word/num/int arithmetic.                                  *)
(* ========================================================================= *)

let mask_red_tac =
  CONV_TAC(DEPTH_CONV(WORD_RED_CONV ORELSEC NUM_RED_CONV ORELSEC INT_RED_CONV) THENC
           WORD_REDUCE_CONV THENC NUM_REDUCE_CONV);;

(* Peel `lo <= b /\ b <= 16` one value at a time; each rule is cheap, whereas
   a single 16-way ARITH_RULE disjunction does not terminate in reasonable time. *)
let one_block_cases16 lo =
  if lo = 16 then
    ARITH_RULE(Printf.sprintf "%d <= b /\\ b <= 16 ==> b = 16" lo |> parse_term)
  else
    ARITH_RULE(Printf.sprintf
      "%d <= b /\\ b <= 16 <=> b = %d \\/ (%d <= b /\\ b <= 16)" lo lo (lo+1)
      |> parse_term);;

let rec MASK_PEEL_TAC lo =
  if lo = 16 then
    DISCH_THEN(fun th -> SUBST1_TAC(MATCH_MP (one_block_cases16 16) th)) THEN
    mask_red_tac
  else
    REWRITE_TAC[one_block_cases16 lo] THEN
    DISCH_THEN(DISJ_CASES_THEN (fun th ->
      (SUBST1_TAC th THEN mask_red_tac)
      ORELSE (MP_TAC th THEN MASK_PEEL_TAC (lo+1))));;

(* Inserting both 64-bit lanes of a 128-bit register discards the original base. *)
let WORD_INSERT_BOTH_LANES = prove
 (`!(b0:int128) (a:int64) (c:int64).
     word_insert ((word_insert b0 (0,64) a):int128) (64,64) c : int128 =
     word_join c a`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* The mask register the routine builds in Q0 (base b0 = the AES ciphertext that
   previously occupied Q0; both its lanes are overwritten by the two csel results)
   equals word (2^(8*byte_len) - 1). *)
(* ONE_BLOCK_MASK_REG moved to gcm_aesgcm_standalone_blocks_helper.ml (unused by AES256_GCM_ENCRYPT_CORRECT). *)

(* The returned byte length: x9 = (8*byte_len) >> 3 = byte_len for byte_len <= 16. *)
let ONE_BLOCK_USHR_BYTELEN = prove
 (`!byte_len. byte_len <= 16
     ==> word_ushr (word (8 * byte_len):int64) 3 = word byte_len`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ushr] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `val (word (8 * byte_len):int64) = 8 * byte_len` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[EXP; ARITH] THEN ARITH_TAC);;

(* The masked ciphertext written by the bif store: masking the already-masked
   block again with the same mask is idempotent. *)
let ONE_BLOCK_MASK_IDEM = prove
 (`!(ct:int128) (mask:int128).
     word_and (word_and mask ct) mask = word_and ct mask`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BITWISE_RULE);;

(* ========================================================================= *)
(* GHASH STEP TACTIC (N=1)                                                    *)
(*                                                                           *)
(* Closes the GHASH conjunct by rewriting the single-block ghash_polyval_acc *)
(* via the ghash_1block_karatsuba spec and its bridge to polyval_dot         *)
(* (GHASH_1BLOCK_KARATSUBA_EQ_POLYVAL_DOT), then the byte-level subword/      *)
(* halfswap normalization, atom/pmul ABBREVs and a final WORD_RULE closure.  *)
(* ========================================================================= *)

let GCM_GHASH_STEP_TAC =
  REWRITE_TAC[ghash_polyval_acc; GSYM WORD_REVERSEFIELDS_XOR_8_128] THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[GSYM(MATCH_MP GHASH_1BLOCK_KARATSUBA_EQ_POLYVAL_DOT th)]) THEN
  REWRITE_TAC[ghash_1block_karatsuba; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  SUBGOAL_THEN
    `word_xor xi (word_xor pt
       (aes256_block_enc ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7
                         rk8 rk9 rk10 rk11 rk12 rk13 rk14)) =
     word_xor xi ct:(128)word`
    (fun th -> REWRITE_TAC[th]) THENL [
    EXPAND_TAC "ct" THEN EXPAND_TAC "s13" THEN
    REWRITE_TAC[aes256_block_enc; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC];
    ALL_TAC
  ] THEN
  ASM_REWRITE_TAC[] THEN
  (* Invert the rev64 + halfswap byte-level expansion via final_xi.          *)
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[REV64_LOWER_LANE; REV64_UPPER_LANE; REV8_JOIN_FOLD] THEN
  MATCH_MP_TAC(MESON[]
    `x = y ==> word_reversefields 8 x = word_reversefields 8 y:(128)word`) THEN
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && rand(concl th) = `final_xi:(128)word`
    then SUBST1_TAC(SYM th) else NO_TAC) THEN
  REWRITE_TAC[WORD_SWAP_HALVES_INVOLUTION] THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[WORD_INSERT_AS_JOIN_1; WORD_INSERT_AS_JOIN_2;
              KAR_SUBWORD_LEMMA; WORD_SWAP_HALVES_INVOLUTION;
              WORD_OR_REFL; WORD_XOR_ASSOC; WORD_SUBWORD_XOR;
              BYTESWAP128_SUBWORD_LO; BYTESWAP128_SUBWORD_HI] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[HALFSWAP_XOR; GSYM WORD_REVERSEFIELDS_XOR_8_128;
              WORD_XOR_0; WORD_XOR_ASSOC;
              REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO;
              REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  REWRITE_TAC[WORD_XOR_ASSOC; KAR_MID_BRIDGE; WORD_SUBWORD_0;
              WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR; GSYM WORD_REVERSEFIELDS_XOR_8_128;
              WORD_XOR_ASSOC; WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[KAR_MID_BRIDGE; WORD_XOR_ASSOC] THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  (* Common-pattern atomic abbreviations (4 = 2N + 2 for N=1) *)
  REWRITE_TAC[BYTESWAP128_SUBWORD_LO; BYTESWAP128_SUBWORD_HI] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[karatsuba_mid] THEN
  ABBREV_TAC `(uA0:(64)word) =
    word_subword (word_reversefields 8 (word_xor (xi:(128)word) ct)) (0,64)` THEN
  ABBREV_TAC `(uA1:(64)word) =
    word_subword (word_reversefields 8 (word_xor (xi:(128)word) ct)) (64,64)` THEN
  ABBREV_TAC `(uD0:(64)word) = word_subword (h:(128)word) (0,64)` THEN
  ABBREV_TAC `(uD1:(64)word) = word_subword (h:(128)word) (64,64)` THEN
  (* 3 inner pmuls (3 = 3N for N=1) *)
  ABBREV_TAC `(p1:(128)word) = word_pmul (uA0:(64)word) (uD0:(64)word)` THEN
  ABBREV_TAC `(p2:(128)word) = word_pmul (uA1:(64)word) (uD1:(64)word)` THEN
  ABBREV_TAC `(p3:(128)word) =
    word_pmul (word_xor (uA0:(64)word) (uA1:(64)word))
              (word_xor (uD0:(64)word) (uD1:(64)word))` THEN
  REWRITE_TAC[DOUBLE_SUBWORD_JOIN; DOUBLE_SUBWORD_JOIN_HI; WORD_SUBWORD_XOR] THEN
  (* 7 z-vars (= 6N+1 for N=1) *)
  ABBREV_TAC `(z1:(64)word) = word_subword (p1:(128)word) (0,64)` THEN
  ABBREV_TAC `(z2:(64)word) = word_subword (p1:(128)word) (64,64)` THEN
  ABBREV_TAC `(z3:(64)word) = word_subword (p2:(128)word) (0,64)` THEN
  ABBREV_TAC `(z4:(64)word) = word_subword (p2:(128)word) (64,64)` THEN
  ABBREV_TAC `(z5:(64)word) = word_subword (p3:(128)word) (0,64)` THEN
  ABBREV_TAC `(z6:(64)word) = word_subword (p3:(128)word) (64,64)` THEN
  ABBREV_TAC `(zD:(64)word) =
    word_subword (word_pmul (z1:(64)word) (word 13979173243358019584:(64)word):(128)word)
                 (0,64)` THEN
  ASM_REWRITE_TAC[] THEN
  (* Normalize the BIG pmul args (XOR-AC) *)
  SUBGOAL_THEN
    `word_pmul (word_xor (z2:(64)word)
                (word_xor z5
                (word_xor z3
                (word_xor z1 zD))))
               (word 13979173243358019584:(64)word):(128)word =
     word_pmul (word_xor (z5:(64)word)
                (word_xor z1
                (word_xor z3
                (word_xor zD z2))))
               (word 13979173243358019584:(64)word):(128)word`
    ASSUME_TAC THENL
    [AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* ABBREV the outer pmul terms and their subword extractions *)
  ABBREV_TAC
    `qBigP = word_pmul
       (word_xor (z5:(64)word) (word_xor z1 (word_xor z3 (word_xor zD z2))))
       (word 13979173243358019584:(64)word):(128)word` THEN
  ABBREV_TAC
    `qSmallP = word_pmul (z1:(64)word)
                        (word 13979173243358019584:(64)word):(128)word` THEN
  ABBREV_TAC `qBigPL = word_subword (qBigP:(128)word) (0,64):(64)word` THEN
  ABBREV_TAC `qBigPH = word_subword (qBigP:(128)word) (64,64):(64)word` THEN
  ABBREV_TAC `qSmallPH = word_subword (qSmallP:(128)word) (64,64):(64)word` THEN
  (* Final closure *)
  BINOP_TAC THENL [CONV_TAC WORD_RULE; CONV_TAC WORD_RULE];;

(* ========================================================================= *)
(* CIPHERTEXT CLOSURE: 1-block instance (shared with GCM_NBLOCK_CT_STEP_TAC). *)
(* For 1-block: ivec_1 = ivec (no gcm_ctr_inc), so no LANE/CTR chain.        *)
(* ========================================================================= *)

let GCM_CT_STEP_TAC = GCM_NBLOCK_CT1_STEP_TAC 1;;

(* ========================================================================= *)
(* GHASH STEP TACTIC (N=1, partial block)                                     *)
(*                                                                           *)
(* As GCM_GHASH_STEP_TAC, but the GHASH input is the MASKED block            *)
(* ctm = word_and ct mask (mask = word (2^(8*byte_len) - 1)).  The symbolic   *)
(* state carries the block as word_and mask ct; the spec uses word_and ct    *)
(* mask, so the opening SUBGOAL bridges the two via commutativity, and the    *)
(* atomic abbreviations are taken over ctm.                                   *)
(* ========================================================================= *)

let GCM_GHASH_STEP_MASKED_TAC =
  REWRITE_TAC[ghash_polyval_acc; GSYM WORD_REVERSEFIELDS_XOR_8_128] THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[GSYM(MATCH_MP GHASH_1BLOCK_KARATSUBA_EQ_POLYVAL_DOT th)]) THEN
  REWRITE_TAC[ghash_1block_karatsuba; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  ABBREV_TAC `mask = word (2 EXP (8 * byte_len) - 1):(128)word` THEN
  ABBREV_TAC `ctm = word_and (ct:(128)word) mask` THEN
  (* Fold the spec-side AES expression to the abbreviated ciphertext `ct`, so
     the postcondition's masked block word_and (word_xor pt aes) mask matches
     ctm = word_and ct mask. *)
  SUBGOAL_THEN
    `word_xor pt (aes256_block_enc ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7
                                   rk8 rk9 rk10 rk11 rk12 rk13 rk14) = ct`
    (fun th -> REWRITE_TAC[th]) THENL [
    MAP_EVERY EXPAND_TAC ["ct"; "s13"] THEN
    REWRITE_TAC[aes256_block_enc; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC];
    ALL_TAC
  ] THEN
  (* The symbolic GHASH input is word_and mask ct; the spec uses word_and ct
     mask = ctm.  Bridge the two via commutativity of word_and. *)
  SUBGOAL_THEN `word_and (mask:(128)word) (ct:(128)word) = ctm`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL [
    EXPAND_TAC "ctm" THEN CONV_TAC WORD_BITWISE_RULE;
    ALL_TAC
  ] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[REV64_LOWER_LANE; REV64_UPPER_LANE; REV8_JOIN_FOLD] THEN
  MATCH_MP_TAC(MESON[]
    `x = y ==> word_reversefields 8 x = word_reversefields 8 y:(128)word`) THEN
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && rand(concl th) = `final_xi:(128)word`
    then SUBST1_TAC(SYM th) else NO_TAC) THEN
  REWRITE_TAC[WORD_SWAP_HALVES_INVOLUTION] THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[WORD_INSERT_AS_JOIN_1; WORD_INSERT_AS_JOIN_2;
              KAR_SUBWORD_LEMMA; WORD_SWAP_HALVES_INVOLUTION;
              WORD_OR_REFL; WORD_XOR_ASSOC; WORD_SUBWORD_XOR;
              BYTESWAP128_SUBWORD_LO; BYTESWAP128_SUBWORD_HI] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[HALFSWAP_XOR; GSYM WORD_REVERSEFIELDS_XOR_8_128;
              WORD_XOR_0; WORD_XOR_ASSOC;
              REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO;
              REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  REWRITE_TAC[WORD_XOR_ASSOC; KAR_MID_BRIDGE; WORD_SUBWORD_0;
              WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR; GSYM WORD_REVERSEFIELDS_XOR_8_128;
              WORD_XOR_ASSOC; WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[KAR_MID_BRIDGE; WORD_XOR_ASSOC] THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  REWRITE_TAC[BYTESWAP128_SUBWORD_LO; BYTESWAP128_SUBWORD_HI] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[karatsuba_mid] THEN
  (* June-2026 HOL base (WORD_SIMPLE_SUBWORD_CONV reorder, b9a430b): the machine
     side leaves the karatsuba-mid pmul's first argument as
       (subword(rev(xi(+)ctm))(64,64) (+) subword(rev xi)(0,64)) (+) subword(rev ctm)(0,64)
     rather than the spec form  subword(rev(xi(+)ctm))(0,64) (+) subword(rev(xi(+)ctm))(64,64).
     Fold it back (pure bitvector identity) so the uA0/uA1/p3 abbreviations fire. *)
  REWRITE_TAC[WORD_BLAST
    `word_xor (word_xor (word_subword (word_reversefields 8 (word_xor (xi:int128) ctm)) (64,64):(64)word)
                        (word_subword (word_reversefields 8 xi) (0,64):(64)word))
              (word_subword (word_reversefields 8 ctm) (0,64):(64)word)
     = word_xor (word_subword (word_reversefields 8 (word_xor xi ctm)) (0,64):(64)word)
                (word_subword (word_reversefields 8 (word_xor xi ctm)) (64,64):(64)word)`] THEN
  ABBREV_TAC `(uA0:(64)word) =
    word_subword (word_reversefields 8 (word_xor (xi:(128)word) ctm)) (0,64)` THEN
  ABBREV_TAC `(uA1:(64)word) =
    word_subword (word_reversefields 8 (word_xor (xi:(128)word) ctm)) (64,64)` THEN
  ABBREV_TAC `(uD0:(64)word) = word_subword (h:(128)word) (0,64)` THEN
  ABBREV_TAC `(uD1:(64)word) = word_subword (h:(128)word) (64,64)` THEN
  ABBREV_TAC `(p1:(128)word) = word_pmul (uA0:(64)word) (uD0:(64)word)` THEN
  ABBREV_TAC `(p2:(128)word) = word_pmul (uA1:(64)word) (uD1:(64)word)` THEN
  ABBREV_TAC `(p3:(128)word) =
    word_pmul (word_xor (uA0:(64)word) (uA1:(64)word))
              (word_xor (uD0:(64)word) (uD1:(64)word))` THEN
  REWRITE_TAC[DOUBLE_SUBWORD_JOIN; DOUBLE_SUBWORD_JOIN_HI; WORD_SUBWORD_XOR] THEN
  ABBREV_TAC `(z1:(64)word) = word_subword (p1:(128)word) (0,64)` THEN
  ABBREV_TAC `(z2:(64)word) = word_subword (p1:(128)word) (64,64)` THEN
  ABBREV_TAC `(z3:(64)word) = word_subword (p2:(128)word) (0,64)` THEN
  ABBREV_TAC `(z4:(64)word) = word_subword (p2:(128)word) (64,64)` THEN
  ABBREV_TAC `(z5:(64)word) = word_subword (p3:(128)word) (0,64)` THEN
  ABBREV_TAC `(z6:(64)word) = word_subword (p3:(128)word) (64,64)` THEN
  ABBREV_TAC `(zD:(64)word) =
    word_subword (word_pmul (z1:(64)word) (word 13979173243358019584:(64)word):(128)word)
                 (0,64)` THEN
  ASM_REWRITE_TAC[] THEN
  (* June-2026 HOL base: both sides' big Barrett pmul has the same argument up to
     XOR-AC, but in different (left-nested) orders that BINOP+WORD_RULE cannot
     bridge through the opaque word_pmul.  Normalize both occurrences to the
     canonical qBigP argument order. *)
  SUBGOAL_THEN
    `word_pmul (word_xor (word_xor (word_xor (word_xor (z2:(64)word) z5) z3) z1) zD)
               (word 13979173243358019584:(64)word):(128)word =
     word_pmul (word_xor (word_xor (word_xor (word_xor (z5:(64)word) z1) z3) zD) z2)
               (word 13979173243358019584:(64)word):(128)word`
    ASSUME_TAC THENL
    [AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
    `qBigP = word_pmul
       (word_xor (word_xor (word_xor (word_xor (z5:(64)word) z1) z3) zD) z2)
       (word 13979173243358019584:(64)word):(128)word` THEN
  ABBREV_TAC
    `qSmallP = word_pmul (z1:(64)word)
                        (word 13979173243358019584:(64)word):(128)word` THEN
  ABBREV_TAC `qBigPL = word_subword (qBigP:(128)word) (0,64):(64)word` THEN
  ABBREV_TAC `qBigPH = word_subword (qBigP:(128)word) (64,64):(64)word` THEN
  ABBREV_TAC `qSmallPH = word_subword (qSmallP:(128)word) (64,64):(64)word` THEN
  BINOP_TAC THENL [CONV_TAC WORD_RULE; CONV_TAC WORD_RULE];;
