(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The part of the proofs of the 8-way AES-GCM encrypt kernels               *)
(* aes128_gcm_enc_alt and aes256_gcm_enc_alt that depends neither on the key *)
(* size nor on the machine code: counter-block and reversefields             *)
(* reconstruction, the kernel's two-pmull GHASH reduction and its POLYVAL    *)
(* meaning, the Karatsuba bridge, and the key-size independent simulation    *)
(* helpers.  It also defines the type of the per-kernel parameters of the    *)
(* shared proof arm/proofs/utils/aes_gcm_enc_alt_proof.ml.  Addresses,       *)
(* labels and step numbers in the comments are those of the AES-256 kernel.  *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/aes_gcm_common.ml";;

(* ------------------------------------------------------------------------- *)
(* The parameters of the shared proof for one kernel.  A kernel proof binds  *)
(* enc_alt_kernel to a record of this type and then loads                    *)
(* arm/proofs/utils/aes_gcm_enc_alt_proof.ml with loadt.  The program        *)
(* counters are offsets of the -DNO_IBT code; the step counts are those of   *)
(* the simulations of that file (see its header).                            *)
(* ------------------------------------------------------------------------- *)

type aes_gcm_enc_alt_kernel =
 { eak_name : string;                   (* the C name *)
   eak_exec : thm * thm option array;   (* ARM_MK_EXEC_RULE of the code *)
   eak_cipher : term;                   (* aes128_cipher or cipher *)
   eak_tmc : term;                      (* the code without the BTI pad *)
   eak_rounds : int;                    (* 10 or 14 *)
   eak_key_split : thm;                 (* KEY11_SPLIT or KEY_SPLIT *)
   eak_cipher_keylist : thm;            (* AESn_CIPHER_KEYLIST *)
   eak_cipher_reconstruct : thm;        (* AESn_CIPHER_RECONSTRUCT *)
   eak_xor_cipher_reconstruct : thm;    (* XOR_AESn_CIPHER_RECONSTRUCT *)
   eak_pc_loop : int;                   (* main-loop top *)
   eak_pc_backedge : int;               (* its b.lt back-edge *)
   eak_pc_prepretail : int;             (* L*_enc_prepretail *)
   eak_pc_tail : int;                   (* L*_enc_tail *)
   eak_pc_end : int;                    (* L*_enc_epilogue *)
   eak_pc_fast : int * int * int * int; (* small paths: tail entries *)
   eak_setup_tail_branch : int;         (* setup: step of b.ge tail *)
   eak_loop_ldp : int * int * int;      (* loop body: incremented ldp steps *)
   eak_loop_backedge : int;             (* loop body: step of the b.lt *)
   eak_prepretail_steps : int;          (* prepretail: steps to the tail *)
   eak_fast_steps : int * int * int * int }   (* small paths: AES steps *)
;;

(* ========================================================================= *)
(* Reversefields equivalences, counter-block reconstruction, and the         *)
(* Karatsuba/GHASH reduction facts the proofs need on top of                 *)
(* arm/proofs/utils/aes_gcm_common.ml.                                       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Reconstruction of high-level concepts from the computed expressions.      *)
(* ------------------------------------------------------------------------- *)

let WORD_SUBWORD_REVERSEFIELDS_32 = prove
 (`word_subword (word_reversefields 32 x:int128) (0,32):int32 =
   word_subword x (96,32) /\
   word_subword (word_reversefields 32 x:int128) (32,32):int32 =
   word_subword x (64,32) /\
   word_subword (word_reversefields 32 x:int128) (64,32):int32 =
   word_subword x (32,32) /\
   word_subword (word_reversefields 32 x:int128) (96,32):int32 =
   word_subword x (0,32)`,
  CONV_TAC WORD_BLAST);;

let WORD_SUBWORD_CTR_BLOCK_32 = prove
 (`word_subword (ctr_block nonce cnt) (0,32):int32 = word cnt /\
   word_subword (ctr_block nonce cnt) (32,32):int32 =
     word_subword nonce (0,32) /\
   word_subword (ctr_block nonce cnt) (64,32):int32 =
     word_subword nonce (32,32) /\
   word_subword (ctr_block nonce cnt) (96,32):int32 =
     word_subword nonce (64,32)`,
  REWRITE_TAC[ctr_block] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[]);;

let CTR_BLOCK_RECONSTRUCT_REV8 = prove
 (`word_join
    (word_join (word_reversefields 8 (word ctr):int32)
               (word_reversefields 8 (word_subword nonce (0,32):int32)):int64)
    (word_join (word_reversefields 8 (word_subword nonce (32,32):int32))
               (word_reversefields 8 (word_subword nonce (64,32):int32)):int64)
    = word_reversefields 8 (ctr_block nonce ctr)`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST);;

let CTR_BLOCK_RECONSTRUCT_REV32 = prove
 (`word_join
    (word_join (word ctr:int32)
               (word_subword nonce (0,32):int32):int64)
    (word_join (word_subword nonce (32,32):int32)
               (word_subword nonce (64,32):int32):int64) =
  word_reversefields 32 (ctr_block nonce ctr)`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST);;

(* ========================================================================= *)
(* GHASH: the kernel's two-pmull reduction and its POLYVAL meaning.          *)
(* ========================================================================= *)

let ghash_reduce_raw = new_definition
 `ghash_reduce_raw p1 p2 p3 =
    let (LO:int128->int64) = \x. word_subword x (0,64) in
    let (ext:int128->int128) =
      \x. word_subword (word_join x x : int256) (64,128) in
    let w = word 13979173243358019584 : int64 in
    let q18 = word_xor (word_xor (word_xor (word_xor p2 p1) p3)
                                 (word_pmul (LO p1) w))
                       (ext p1) in
    word_xor (word_xor p3 (word_pmul (LO q18) w)) (ext q18) : int128`;;

(* ghash_reduce_raw is kept as a fold target.  Its body is the term that     *)
(* symbolic execution of the kernel's 8-instruction reduction (ldr d16,[x10] *)
(* through the final eor3 into v19) produces for Q19, so RECON_GRR can fold  *)
(* that raw reduce back into a named form by GSYM, in the main loop, the     *)
(* prepretail and the tail and small-path arms.  The shared                  *)
(* polyval_reduce_g2 arranges the same computation differently, so folding   *)
(* into it directly would first need the emitted term normalised.            *)
(* GHASH_REDUCE_RAW_IS_POLYVAL_G2 relates the two (ghash_reduce_raw p1 p2 p3 *)
(* = polyval_reduce_g2 p1 p3 p2), and the per-block folds reach polyval_dot  *)
(* through it, so no second GHASH semantics arises.                          *)

let GHASH_REDUCE_RAW_IS_POLYVAL_G2 = prove
 (`!p1 p2 p3. ghash_reduce_raw p1 p2 p3 = polyval_reduce_g2 p1 p3 p2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ghash_reduce_raw; polyval_reduce_g2] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  ABBREV_TAC
   `w1 = (word_pmul:int64->int64->int128)
      (word_subword (p1:int128) (0,64)) (word 13979173243358019584)` THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
   `word_xor (word_xor (word_xor (word_xor (a:int64) b) c) d) e =
    word_xor (word_xor d e) (word_xor (word_xor b c) a)`] THEN
  CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* The Karatsuba multiply-accumulate fold.                                   *)
(*                                                                           *)
(* Given the three Karatsuba partial products of a single 128x128 carryless  *)
(* multiply a * b -- lo*lo, the cross term (a_lo^a_hi)*(b_lo^b_hi), and      *)
(* hi*hi -- feeding the reduce in the Q17 (hi) / Q18 (mid) / Q19 (lo) order  *)
(* the hardware uses (pmull -> lo lane, pmull2 -> hi lane, pmull of the      *)
(* eor'd halves -> cross/mid lane), the reduce computes exactly the polyval  *)
(* "dot" product polyval_dot a b = prop3(pmul a b):                          *)
(*                                                                           *)
(*        ghash_reduce_raw <lo*lo> <cross> <hi*hi>  =  polyval_dot a b       *)
(*                                                                           *)
(* Proof chain: GHASH_REDUCE_RAW_IS_POLYVAL_G2 turns ghash_reduce_raw into   *)
(* polyval_reduce_g2 (with the p2<->p3 swap that reorders cross/hi into g2's *)
(* hi,lo,mid slots), POLYVAL_REDUCE_G2 rewrites that to polyval_reduce_prop3 *)
(* of the reassembled 256-bit product, and GSYM PMUL_KARATSUBA_JOIN          *)
(* collapses the three partial products back into the single word_pmul a b   *)
(* inside polyval_dot.  The two REWRITE_TAC calls must stay separate:        *)
(* putting POLYVAL_REDUCE_G2 into the first rewrite list makes it fire       *)
(* before the swap settles and the proof diverges.                           *)
(*                                                                           *)
(* This is the per-block fold primitive the main-loop, prepretail and tail   *)
(* folds compose: each GHASH block is `word_pmul (acc_xor_block) (h_power    *)
(* ...)`; the batched multi-block accumulation over v8..v15 then closes with *)
(* GHASH_POLYVAL_ACC_BATCHED from common/polyval_ghash.ml (which reduces     *)
(* `ghash_polyval_acc h a (CONS b bs)` to a prop3 of the pmul + ghash_wide   *)
(* sum), and NIST_DOT_IS_POLYVAL_DOT / NIST_GHASH_IS_POLYVAL bridge the      *)
(* polyval accumulator to the nist_ghash tag.                                *)
(* ------------------------------------------------------------------------- *)

let GHASH_REDUCE_RAW_KARATSUBA_IS_DOT = prove
 (`!a b:int128.
    ghash_reduce_raw
      (word_pmul (word_subword a (0,64):int64)
                 (word_subword b (0,64):int64):int128)
      (word_pmul (word_xor (word_subword a (0,64):int64)
                           (word_subword a (64,64):int64))
                 (word_xor (word_subword b (0,64):int64)
                           (word_subword b (64,64):int64)):int128)
      (word_pmul (word_subword a (64,64):int64)
                 (word_subword b (64,64):int64):int128)
    = polyval_dot a b`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_IS_POLYVAL_G2] THEN
  REWRITE_TAC[POLYVAL_REDUCE_G2; polyval_dot] THEN
  REWRITE_TAC[GSYM(REWRITE_RULE[LET_DEF;LET_END_DEF] PMUL_KARATSUBA_JOIN)]);;

(* ------------------------------------------------------------------------- *)
(* Stepping helpers.                                                         *)
(*                                                                           *)
(* The main-loop body reloads 8 plaintext blocks with `ldp q_even,q_odd,     *)
(* [x0],#32` (steps 263/295/303/304).  Because X0 post-increments, the       *)
(* second element of each later pair is read at `word_add (word_add in_p     *)
(* (word ...)) (word 16)`, where the offset arithmetic (e.g.                 *)
(* `(128*(i+1)+64)+48`) is not reduced to the literal `128*(i+1)+112` that   *)
(* the input-block reads use.  The stepper's memory resolution needs a       *)
(* syntactic address match, so the load stays opaque (`read(memory..)        *)
(* s_prev`) and DISCARD_OLDSTATE drops the ciphertext-register fact.  (The   *)
(* first ldp, blocks 0/1, resolves directly because X0 is still the base     *)
(* address there.)                                                           *)
(*                                                                           *)
(* LDP_STEP4_TAC, used only at the incremented ldps, re-derives the 8        *)
(* plaintext reads at the current state from the persistent quantified       *)
(* in-memory forall (INBLOCKS_TAC: the specific s0 facts get dropped, the    *)
(* forall does not), steps verbosely (no automatic discard), flattens the    *)
(* nested word_adds, normalises the offset arithmetic to the literal form    *)
(* (NORMOFF_RULE), resolves the now-matching memory reads and then discards  *)
(* the old state.  NORMOFF_RULE reduces `word (a + c1 + c2 + ...)` offsets;  *)
(* is_inp_memfact selects the memory equations used to substitute the loads. *)
(* NSTEP_G_TAC is the ordinary per-step chain (flatten + NORMOFF + subword)  *)
(* for all other instructions.                                               *)
(* ------------------------------------------------------------------------- *)

let NORMOFF_RULE =
  CONV_RULE(ONCE_DEPTH_CONV(fun tm -> match tm with
      Comb(Const("word",_),_) ->
        (RAND_CONV(REWRITE_CONV[GSYM ADD_ASSOC] THENC DEPTH_CONV
                   NUM_ADD_CONV)) tm
    | _ -> failwith "NORMOFF"));;

(* Selects only the freshly re-derived input-block reads (`read (memory :>   *)
(* bytesN ..) s = inblock <idx>`), which LDP_STEP4_TAC substitutes into the  *)
(* ldp second-element load.  The guard `is_var(fst(strip_comb rhs))` on the  *)
(* right-hand side is essential: without it every `read(memory..) s = v`     *)
(* fact would be selected, and REWRITE_RULE memfacts would rewrite each      *)
(* read-only key/mod/tag/ivec/htable fact with itself to `T`, deleting the   *)
(* read-only memory facts the postcondition needs (they are never            *)
(* re-derived, unlike the input reads, which INBLOCKS_TAC re-asserts at each *)
(* call).  Input reads carry the abstract value `inblock j` (a variable      *)
(* applied to arguments); all read-only facts carry constant-headed values   *)
(* (word_reversefields/word/...).                                            *)
let is_inp_memfact th =
  match concl th with
    Comb(Comb(Const("=",_), Comb(Comb(Const("read",_),
      Comb(Comb(Const(":>",_),Const("memory",_)),_)), _)), rhs) ->
        is_var(fst(strip_comb rhs))
  | _ -> false;;

(* ------------------------------------------------------------------------- *)
(* ASSUMPTION_STATE_UPDATE_TAC re-stamps every surviving assumption from the *)
(* previous state to the new one at each step with its right-hand side       *)
(* unchanged, so a fact already in subword-normal form comes back still      *)
(* normal.  WORD_SIMPLE_SUBWORD_CONV can only fire on a `word_subword _      *)
(* (NUMERAL,NUMERAL)` subterm (its outer match fails otherwise), so on a     *)
(* term without that shape TOP_DEPTH_CONV of it returns REFL and CONV_RULE   *)
(* is the identity.  SUBWORD_NORM_RULE therefore guards the conversion with  *)
(* a short-circuiting find_term for exactly that shape: for every theorem th *)
(* it returns what `CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) th`   *)
(* returns, without re-traversing the stable carried facts at every step.    *)
(* Used by NSTEP_TAC, NSTEP_G_TAC and NSTEP_GP_TAC below.                    *)
(* ------------------------------------------------------------------------- *)
let has_word_subword_numpair =
  can (find_term (fun t -> match t with
      Comb(Comb(Const("word_subword",_),_),
           Comb(Comb(Const(",",_),Comb(Const("NUMERAL",_),_)),
                Comb(Const("NUMERAL",_),_))) -> true
    | _ -> false));;

let SUBWORD_NORM_RULE th =
  if has_word_subword_numpair (concl th)
  then CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) th
  else th;;

(* has_wadd_nest: the same kind of guard for the word_add-nest flatten in    *)
(* NSTEP_GP_TAC (NSTEP_GP_WADD_RULE).  That REWRITE_RULE rewrites `word_add  *)
(* (word_add b (word m)) (word nn) -> word_add b (word(m+nn))`, which only   *)
(* fires on a register-pointer fact with the doubly nested word_add shape    *)
(* left by a post-increment ldr/str advancing X0/X2; on every other fact it  *)
(* returns the theorem unchanged, so the guard skips the rewrite there.      *)
let has_wadd_nest =
  can (find_term (fun t -> match t with
      Comb(Comb(Const("word_add",_),
             Comb(Comb(Const("word_add",_),_),
                  Comb(Const("word",_),_))),
           Comb(Const("word",_),_)) -> true
    | _ -> false));;

(* has_word_of_sum: the corresponding guard for NORMOFF_RULE in              *)
(* NSTEP_GP_TAC.  NORMOFF_RULE only rewrites a `word (t)` subterm whose      *)
(* argument t is a sum (`_ + _`), i.e. an offset not yet collapsed to a      *)
(* literal such as `word (128 * (k+1) + 16 + 32)`; facts without such a      *)
(* subterm are returned unchanged.                                           *)
let has_word_of_sum =
  can (find_term (fun t -> match t with
      Comb(Const("word",_), Comb(Comb(Const("+",_),_),_)) -> true
    | _ -> false));;

(* WB_WADD_RULE: the word_add-nest flatten applied after each step by        *)
(* NSTEP_TAC and NSTEP_G_TAC (NSTEP_GP_TAC applies the same rewrite as       *)
(* NSTEP_GP_WADD_RULE, guarded by has_wadd_nest).                            *)
let WB_WADD_RULE = REWRITE_RULE[WORD_RULE
  `word_add (word_add b (word m)) (word nn):int64 = word_add b (word(m+nn))`];;

(* ------------------------------------------------------------------------- *)
(* Guarded body stepper.                                                     *)
(*                                                                           *)
(* The GHASH accumulators Q17/Q18/Q19 are word_join-headed Karatsuba lane    *)
(* sums.  WORD_SIMPLE_SUBWORD_CONV pushes word_subword into the joins,       *)
(* collapsing `word_subword(word_join a b)(0,64)` -> b etc.  That would      *)
(* destroy the `LO p1` / `ext p1` structure of ghash_reduce_raw's            *)
(* definition, and the body-end Q19 residual could then not be folded back   *)
(* to ghash_reduce_raw.                                                      *)
(*                                                                           *)
(* NSTEP_G_TAC is NSTEP_TAC with all three per-step normalisations skipped   *)
(* on any assumption that mentions read Q17, Q18 or Q19 (is_ghash_acc).  The *)
(* word_add flatten and NORMOFF are the identity on those word_join /        *)
(* word_subword terms anyway, and skipping the subword pass keeps their      *)
(* ext/LO structure, so the final Q19 stays foldable.  The v0..v15 counter   *)
(* and ciphertext facts (all other registers) are normalised as by           *)
(* NSTEP_TAC.                                                                *)
(* ------------------------------------------------------------------------- *)
let is_ghash_acc th =
  let c = concl th in
  can (find_term (fun t -> match t with
      Comb(Const("read",_), r) ->
        (match r with
         | Const("Q17",_) | Const("Q18",_) | Const("Q19",_) -> true
         | _ -> false)
    | _ -> false)) c;;

let INBLOCKS_TAC sname =
  let sv = mk_var(sname,`:armstate`) in
  let concl_tm = subst[sv,`s:armstate`]
   `read (memory :> bytes128 (word_add in_p (word (128 * (i + 1))))) s =
    inblock (8 * (i + 1)) /\
    read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 16)))) s =
    inblock (8 * (i + 1) + 1) /\
    read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 32)))) s =
    inblock (8 * (i + 1) + 2) /\
    read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 48)))) s =
    inblock (8 * (i + 1) + 3) /\
    read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 64)))) s =
    inblock (8 * (i + 1) + 4) /\
    read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 80)))) s =
    inblock (8 * (i + 1) + 5) /\
    read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 96)))) s =
    inblock (8 * (i + 1) + 6) /\
    read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 112)))) s =
    inblock (8 * (i + 1) + 7)` in
  SUBGOAL_THEN concl_tm STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE
     `128 * (i + 1) + 16 = 16 * (8 * (i + 1) + 1) /\
      128 * (i + 1) + 32 = 16 * (8 * (i + 1) + 2) /\
      128 * (i + 1) + 48 = 16 * (8 * (i + 1) + 3) /\
      128 * (i + 1) + 64 = 16 * (8 * (i + 1) + 4) /\
      128 * (i + 1) + 80 = 16 * (8 * (i + 1) + 5) /\
      128 * (i + 1) + 96 = 16 * (8 * (i + 1) + 6) /\
      128 * (i + 1) + 112 = 16 * (8 * (i + 1) + 7)`] THEN
    REWRITE_TAC[ARITH_RULE `128 * a = 16 * 8 * a`] THEN
    (* Each obligation is the antecedent of an input fact about the state    *)
    (* (the input facts of the loop body, see INPUT_LEG_TAC, are one-block   *)
    (* facts and the input fact of the rest), for the block 8*(i+1)+b; it    *)
    (* follows from i < k and 8*(k+1) <= nb alone, so only those two         *)
    (* hypotheses are undischarged before ARITH_TAC (the same idiom as       *)
    (* flag_arith in the main-loop body).  An input fact that does not cover *)
    (* the block fails the ARITH_TAC, and FIRST_ASSUM tries the next one.    *)
    REPEAT CONJ_TAC THEN
    FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN
      UNDISCH_TAC `8 * (k + 1) <= nb` THEN UNDISCH_TAC `(i:num) < k` THEN
      ARITH_TAC);
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* Flag-close lemmas for the main-loop body.                                 *)
(*                                                                           *)
(* The loop back-edge is a signed pointer compare `cmp x0,x5; b.lt` at       *)
(* pc+0x9a0/0xa0c: X0 = in_p + 128*(i+2) (four `ldp [x0],#32` past the loop  *)
(* top), X5 = end_p.  After the cheap-close ASM_REWRITE, the invariant's     *)
(* flag conjunct q(i+1) has been reduced to the raw NF<>VF biconditional     *)
(* over `word_sub X0 end_p`.  BRIDGE_GE recognises that biconditional as the *)
(* signed GE `ival end_p <= ival X0`; IVAL_PTR_ADD linearises each additive  *)
(* ival under the buffer-end no-wrap bound `val in_p + 128*(k+1) < 2^63`;    *)
(* INT/ARITH then reduces the whole thing to `i + 1 = k` using the body      *)
(* hypothesis `i < k`.  The no-wrap bound is an antecedent of MAIN_LOOP.     *)
(* ------------------------------------------------------------------------- *)

let BRIDGE_GE = prove
 (`!a c:int64.
     ((ival (word_sub a c) < &0) <=>
      ~(ival a - ival c = ival (word_sub a c))) <=> ival c <= ival a`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* SETUP branch-discharge lemmas.                                            *)
(*                                                                           *)
(* The pipeline-fill setup has two `cmp x0,x5; b.ge` guards, the tail check  *)
(* at 0x448/0x44c and the prepretail check at 0x480/0x4bc, both comparing    *)
(* the running input pointer X0 against the loop-end pointer                 *)
(*      X5 = ((len_bits DIV 8) - 1) & ~127  +  in_p                          *)
(* (hardware: sub x5,x5,#1; and x5,x5,#0xffffffffffffff80; add x5,x5,x0 at   *)
(* 0x6c/0x70/0x74, with x5 initialised to x9 = word(len_bits DIV 8), the     *)
(* byte length 16*nb).  The first guard falls through for nb > 8 and the     *)
(* second for nb > 16, i.e. when k >= 1 with k = (nb-1) DIV 8 - 1.           *)
(*                                                                           *)
(* X5_END_PTR_GEN: for 1 <= nb (and 16*nb < 2^64) the round-down mask gives  *)
(* X5 = in_p + 128*((nb-1) DIV 8).  With 8*(k+1) < nb <= 8*(k+2) this is the *)
(* loop-end pointer end_p = in_p + 128*(k+1) that MAIN_LOOP's antecedent     *)
(* pins (SETUP_X5_END_GEN below): the last group of 1..8 blocks is not run   *)
(* by the main loop but drained by the prepretail and the tail.  Proof via   *)
(* WORD_AND_NOT_MASK_WORD (the clear-low-7-bits lemma) + VAL_WORD_SUB_CASES. *)
(* ------------------------------------------------------------------------- *)
let X5_END_PTR_GEN = prove
 (`!(in_p:int64) nb.
     1 <= nb /\ 16 * nb < 2 EXP 64
     ==> word_add
           (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                     (word 18446744073709551488))
           in_p =
         word_add in_p (word (128 * ((nb - 1) DIV 8)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 16 * nb` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `val(word_sub (word (16 * nb)) (word 1):int64) = 16 * nb - 1`
   ASSUME_TAC THENL
   [SUBGOAL_THEN `val(word (16 * nb):int64) = 16 * nb` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD_1] THEN
    COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_ADD_SYM] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `word_and (word_sub (word (16 * nb)) (word 1))
             (word 18446744073709551488):int64 =
    word(2 EXP 7 * (val(word_sub (word (16 * nb)) (word 1):int64)
                    DIV 2 EXP 7))`
   SUBST1_TAC THENL
   [SUBGOAL_THEN `word 18446744073709551488:int64 = word_not(word(2 EXP 7 - 1))`
      SUBST1_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
    REWRITE_TAC[WORD_AND_NOT_MASK_WORD];
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 7 = 128`] THEN
    SUBGOAL_THEN
      `16 * nb - 1 = 128 * ((nb-1) DIV 8) + (16 * ((nb-1) MOD 8) + 15)`
      SUBST1_TAC THENL
     [MP_TAC(SPECL [`nb - 1`; `8`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `128 * ((nb-1) DIV 8) = ((nb-1) DIV 8) * 128` SUBST1_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN
    SUBGOAL_THEN `(16 * ((nb-1) MOD 8) + 15) DIV 128 = 0` SUBST1_TAC THENL
     [REWRITE_TAC[DIV_EQ_0; ARITH_EQ] THEN
      MP_TAC(SPECL [`nb - 1`; `8`] DIVISION) THEN ARITH_TAC;
      ARITH_TAC]]);;

(* end_p = in_p + 128*(k+1) is strictly above in_p (signed), since 128*(k+1) *)
(* >= 128 > 0 and there is no signed wrap.  So the first guard's `cmp x0,x5; *)
(* b.ge` with X0 = in_p does not take the branch.  The second guard (X0 =    *)
(* in_p+128) is SETUP_GE_FALSE_2 below, which needs ~(k = 0).                *)
let SETUP_GE_FALSE = prove
 (`!(in_p:int64) k.
     val in_p + 128 * (k + 1) < 2 EXP 63
     ==> ~(ival (word_add in_p (word (128 * (k + 1)))) <= ival in_p)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`in_p:int64`; `128 * (k + 1)`] IVAL_PTR_ADD) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ival(in_p:int64) = &(val in_p)` ASSUME_TAC THENL
   [REWRITE_TAC[INT_IVAL; DIMINDEX_64] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_OF_NUM_LE]) THEN ASM_ARITH_TAC);;

(* nb = 2 selector: `cmp x9,#0x20; b.eq L256_enc_small_2` at 0x1534/0x1538   *)
(* (inside L256_enc_small; x9 = word(16*nb)) is not taken for nb <> 2.       *)
let DISPATCH_NOT_TAKEN = prove
 (`!nb:num. 128 * nb < 2 EXP 64 /\ ~(nb = 2)
    ==> (val (word_sub (word ((128 * nb) DIV 8):int64) (word 32)) = 0 <=> F)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 16 * nb` SUBST1_TAC THENL
  [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `16 * nb < 2 EXP 64 /\ 32 < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VAL_EQ_0] THEN
  SUBGOAL_THEN
    `(word_sub (word (16 * nb):int64) (word 32) = word 0) <=>
     (word (16*nb):int64 = word 32)`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64; MOD_LT] THEN
  ASM_ARITH_TAC);;

(* The taken twin of DISPATCH_NOT_TAKEN: for nb = 2 the `cmp x9,#0x20; b.eq  *)
(* L256_enc_small_2` at 0x1534/0x1538 is taken (x9 = (128*2) DIV 8 = 32).    *)
let DISPATCH_TAKEN = prove
 (`!nb:num. nb = 2
    ==> (val (word_sub (word ((128 * nb) DIV 8):int64) (word 32)) = 0 <=> T)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 32` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_sub (word 32:int64) (word 32) = word 0`] THEN
  REWRITE_TAC[VAL_WORD_0]);;

(* The nb <= 4 entry test `cmp x9,#0x40; b.le L256_enc_small` at             *)
(* pc+0x4c/0x50 (x9 = word(16*nb)).  DISPATCH4_NOT_TAKEN and DISPATCH4_TAKEN *)
(* resolve the ZF disjunct of its condition (x9 = 64 iff nb = 4);            *)
(* DISPATCH_SMALL_NOT_TAKEN / DISPATCH_SMALL_TAKEN below resolve the signed  *)
(* less-than disjunct.  For nb = 4 the b.le is taken and the three b.eq      *)
(* tests in L256_enc_small fall through to L256_enc_small_4.                 *)
let DISPATCH4_NOT_TAKEN = prove
 (`!nb:num. 128 * nb < 2 EXP 64 /\ ~(nb = 4)
    ==> (val (word_sub (word ((128 * nb) DIV 8):int64) (word 64)) = 0 <=> F)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 16 * nb` SUBST1_TAC THENL
  [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `16 * nb < 2 EXP 64 /\ 64 < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VAL_EQ_0] THEN
  SUBGOAL_THEN
    `(word_sub (word (16 * nb):int64) (word 64) = word 0) <=>
     (word (16*nb):int64 = word 64)`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64; MOD_LT] THEN
  ASM_ARITH_TAC);;

(* The taken twin: for nb = 4 the ZF disjunct of the b.le at 0x50 holds (x9  *)
(* = (128*4) DIV 8 = 64).                                                    *)
let DISPATCH4_TAKEN = prove
 (`!nb:num. nb = 4
    ==> (val (word_sub (word ((128 * nb) DIV 8):int64) (word 64)) = 0 <=> T)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 64` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_sub (word 64:int64) (word 64) = word 0`] THEN
  REWRITE_TAC[VAL_WORD_0]);;

(* nb = 1 selector: `cmp x9,#0x10; b.eq L256_enc_small_1` at 0x152c/0x1530,  *)
(* the first test inside L256_enc_small: not taken for nb <> 1, taken for    *)
(* nb = 1 (DISPATCH1_TAKEN).  x9 = word(16*nb).                              *)
let DISPATCH1_NOT_TAKEN = prove
 (`!nb:num. 128 * nb < 2 EXP 64 /\ ~(nb = 1)
    ==> (val (word_sub (word ((128 * nb) DIV 8):int64) (word 16)) = 0 <=> F)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 16 * nb` SUBST1_TAC THENL
  [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `16 * nb < 2 EXP 64 /\ 16 < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VAL_EQ_0] THEN
  SUBGOAL_THEN
    `(word_sub (word (16 * nb):int64) (word 16) = word 0) <=>
     (word (16*nb):int64 = word 16)`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64; MOD_LT] THEN
  ASM_ARITH_TAC);;

let DISPATCH1_TAKEN = prove
 (`!nb:num. nb = 1
    ==> (val (word_sub (word ((128 * nb) DIV 8):int64) (word 16)) = 0 <=> T)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 16` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_sub (word 16:int64) (word 16) = word 0`] THEN
  REWRITE_TAC[VAL_WORD_0]);;

(* nb = 3 selector: `cmp x9,#0x30; b.eq L256_enc_small_3` at 0x153c/0x1540.  *)
let DISPATCH3_NOT_TAKEN = prove
 (`!nb:num. 128 * nb < 2 EXP 64 /\ ~(nb = 3)
    ==> (val (word_sub (word ((128 * nb) DIV 8):int64) (word 48)) = 0 <=> F)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 16 * nb` SUBST1_TAC THENL
  [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `16 * nb < 2 EXP 64 /\ 48 < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VAL_EQ_0] THEN
  SUBGOAL_THEN
    `(word_sub (word (16 * nb):int64) (word 48) = word 0) <=>
     (word (16*nb):int64 = word 48)`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64; MOD_LT] THEN
  ASM_ARITH_TAC);;

let DISPATCH3_TAKEN = prove
 (`!nb:num. nb = 3
    ==> (val (word_sub (word ((128 * nb) DIV 8):int64) (word 48)) = 0 <=> T)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 48` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_sub (word 48:int64) (word 48) = word 0`] THEN
  REWRITE_TAC[VAL_WORD_0]);;

(* nb >= 5 (x9 = 16*nb >= 80 > 64): the signed less-than disjunct is F, so   *)
(* with DISPATCH4_NOT_TAKEN killing the ZF disjunct the b.le is not taken.   *)
(* Used by the SETUP legs and SETUP0.                                        *)
let DISPATCH_SMALL_NOT_TAKEN = prove
 (`!nb:num. 128 * nb < 2 EXP 64 /\ 5 <= nb
    ==> (~(ival (word_sub (word ((128 * nb) DIV 8):int64) (word 64)) < &0 <=>
           ~(ival (word ((128 * nb) DIV 8):int64) - &64 =
             ival (word_sub (word ((128 * nb) DIV 8):int64) (word 64))))
               <=> F)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 16 * nb` SUBST1_TAC THENL
  [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `64 <= 16 * nb` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `16 * nb < 2 EXP 63` ASSUME_TAC THENL
  [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `16 * nb - 64 < 2 EXP 63` ASSUME_TAC THENL
  [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word (16 * nb):int64) (word 64) = word (16 * nb - 64)`
    SUBST1_TAC THENL
   [ASM_SIMP_TAC[WORD_SUB]; ALL_TAC] THEN
  ASM_SIMP_TAC[IVAL_WORD_SMALL; INT_OF_NUM_SUB] THEN
  MP_TAC(ASSUME `64 <= 16 * nb`) THEN REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
  INT_ARITH_TAC);;

(* nb in {1,2,3} (x9 = 16*nb < 64): the signed less-than disjunct is T, so   *)
(* the b.le is taken (DISPATCH4_NOT_TAKEN gives F for the ZF disjunct).      *)
(* nb = 4 is taken by DISPATCH4_TAKEN alone.                                 *)
let DISPATCH_SMALL_TAKEN = prove
 (`!nb:num. 1 <= nb /\ nb <= 3
    ==> (~(ival (word_sub (word ((128 * nb) DIV 8):int64) (word 64)) < &0 <=>
           ~(ival (word ((128 * nb) DIV 8):int64) - &64 =
             ival (word_sub (word ((128 * nb) DIV 8):int64) (word 64))))
               <=> T)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 16 * nb` SUBST1_TAC THENL
  [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `16 * nb < 64 /\ 16 * nb < 2 EXP 63 /\ 64 < 2 EXP 63`
    STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[IVAL_WORD_SMALL; IVAL_WORD_SUB_SMALL] THEN
  MP_TAC(ASSUME `16 * nb < 64`) THEN REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN
  INT_ARITH_TAC);;

let SETUP_GE_FALSE_2 = prove
 (`!(in_p:int64) k.
     ~(k = 0) /\ val in_p + 128 * (k + 1) < 2 EXP 63
     ==> ~(ival (word_add in_p (word (128 * (k + 1)))) <=
           ival (word_add in_p (word 128)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`in_p:int64`; `128 * (k + 1)`] IVAL_PTR_ADD) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`in_p:int64`; `128`] IVAL_PTR_ADD) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST_ALL_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_OF_NUM_LE]) THEN ASM_ARITH_TAC);;

let SETUP_X5_END_GEN = prove
 (`!(in_p:int64) k nb.
     8 * (k + 1) < nb /\ nb <= 8 * (k + 2) /\
     val in_p + 128 * (k + 1) < 2 EXP 63
     ==> word_add
           (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                     (word 18446744073709551488)) in_p =
         word_add in_p (word (128 * (k + 1)):int64)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`in_p:int64`; `nb:num`] X5_END_PTR_GEN) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_ARITH_TAC;
      UNDISCH_TAC `nb <= 8 * (k + 2)` THEN
      UNDISCH_TAC `val(in_p:int64) + 128 * (k + 1) < 2 EXP 63` THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(nb - 1) DIV 8 = k + 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC]);;

(* SETUP_BRANCH_COND_FALSE_GEN collapses the first guard's condition (the    *)
(* exact NF<>VF biconditional the stepper emits for `cmp x0,x5; b.ge` at     *)
(* 0x448/0x44c with X0 = in_p) to F, so the conditional PC resolves to the   *)
(* fall-through.  X5 is still the raw hardware form ((128*nb) DIV 8 - 1) &   *)
(* ~127 + in_p; SETUP_X5_END_GEN normalises it to end_p, and BRIDGE_GE +     *)
(* SETUP_GE_FALSE finish.  SETUP_BRANCH_COND_FALSE_2_GEN is the same for the *)
(* second guard (0x480/0x4bc, X0 = in_p+128, k <> 0).                        *)
let SETUP_BRANCH_COND_FALSE_GEN = prove
 (`!(in_p:int64) k nb.
     8 * (k + 1) < nb /\ nb <= 8 * (k + 2) /\
     val in_p + 128 * (k + 1) < 2 EXP 63
     ==> ((ival (word_sub in_p
                  (word_add
                    (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                              (word 18446744073709551488))
                    in_p)) < &0 <=>
           ~(ival in_p -
             ival (word_add
                    (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                              (word 18446744073709551488))
                    in_p) =
             ival (word_sub in_p
                    (word_add
                      (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                                (word 18446744073709551488))
                      in_p)))) <=> F)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SETUP_X5_END_GEN] THEN
  REWRITE_TAC[BRIDGE_GE] THEN
  REWRITE_TAC[MATCH_MP SETUP_GE_FALSE (ASSUME
    `val(in_p:int64) + 128 * (k + 1) < 2 EXP 63`)]);;

let SETUP_BRANCH_COND_FALSE_2_GEN = prove
 (`!(in_p:int64) k nb.
     ~(k = 0) /\ 8 * (k + 1) < nb /\ nb <= 8 * (k + 2) /\
     val in_p + 128 * (k + 1) < 2 EXP 63
     ==> ((ival (word_sub (word_add in_p (word 128))
                  (word_add
                    (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                              (word 18446744073709551488))
                    in_p)) < &0 <=>
           ~(ival (word_add in_p (word 128)) -
             ival (word_add
                    (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                              (word 18446744073709551488))
                    in_p) =
             ival (word_sub (word_add in_p (word 128))
                    (word_add
                      (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                                (word 18446744073709551488))
                      in_p)))) <=> F)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SETUP_X5_END_GEN] THEN
  REWRITE_TAC[BRIDGE_GE] THEN
  REWRITE_TAC[MATCH_MP SETUP_GE_FALSE_2 (CONJ (ASSUME `~(k = 0)`) (ASSUME
    `val(in_p:int64) + 128 * (k + 1) < 2 EXP 63`))]);;

(* SETUP_BRANCH_COND_TRUE_2: the second setup guard (b.ge at 0x4bc, the cmp  *)
(* with X0 = word_add in_p (word 128) after consuming one 8-block group) is  *)
(* taken for groups = 1 (k = 0): the round-down end_p = word_add in_p        *)
(* (word(128*(k+1))) = in_p+128 at k = 0, so X0 = end_p and the b.ge         *)
(* condition collapses to T, giving PC = 0xa10 (PREPRETAIL).  The            *)
(* counterpart of WB_BRANCH_COND_TRUE (first guard) for the second guard.    *)
let SETUP_BRANCH_COND_TRUE_2 = prove
 (`!(in_p:int64) k nb.
     k = 0 /\ 8 * (k + 1) < nb /\ nb <= 8 * (k + 2) /\
     val in_p + 128 * (k + 1) < 2 EXP 63
     ==> ((ival (word_sub (word_add in_p (word 128))
                  (word_add
                    (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                              (word 18446744073709551488))
                    in_p)) < &0 <=>
           ~(ival (word_add in_p (word 128)) -
             ival (word_add
                    (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                              (word 18446744073709551488))
                    in_p) =
             ival (word_sub (word_add in_p (word 128))
                    (word_add
                      (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                                (word 18446744073709551488))
                      in_p)))) <=> T)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SETUP_X5_END_GEN] THEN
  ASM_REWRITE_TAC[ARITH_RULE `128 * (0 + 1) = 128`] THEN
  REWRITE_TAC[WORD_SUB_REFL; INT_SUB_REFL; IVAL_WORD_0] THEN
  INT_ARITH_TAC);;

(* SETUP-specific input-block re-derivation and ldp stepper.  In the setup   *)
(* the 8 plaintext blocks live at in_p + 16*j (j = 0..7), not at the loop    *)
(* body's 128*(i+1)+off.  SETUP_INBLOCKS_TAC re-asserts all 8 reads at state *)
(* `sname` from the persistent quantified input-forall; LDP_SETUP_TAC is     *)
(* LDP_STEP4_TAC with that variant.  The setup legs use it at all four `ldp  *)
(* [x0],#32` (steps 263/264/272/273), including the first, whose block-0     *)
(* load at the bare in_p needs the address normalisation below.              *)
let SETUP_INBLOCKS_TAC sname =
  let sv = mk_var(sname,`:armstate`) in
  let concl_tm = subst[sv,`s:armstate`]
   `read (memory :> bytes128 (word_add in_p (word (16 * 0)))) s = inblock 0 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 1)))) s = inblock 1 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 2)))) s = inblock 2 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 3)))) s = inblock 3 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 4)))) s = inblock 4 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 5)))) s = inblock 5 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 6)))) s = inblock 6 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 7)))) s = inblock 7` in
  SUBGOAL_THEN concl_tm STRIP_ASSUME_TAC THENL
   [(* Each obligation is the antecedent of an input fact about the state,   *)
    (* for a literal block b = 0..7; it follows from 8 * (k + 1) <= nb       *)
    (* alone, so only that hypothesis is undischarged before ARITH_TAC       *)
    (* (ASM_ARITH_TAC would consider every carried fact).  All callers       *)
    (* (SETUP_GEN, SETUP_G1 and their _SAFE versions) have that hypothesis.  *)
    (* An input fact that does not cover the block fails the ARITH_TAC, and  *)
    (* FIRST_ASSUM tries the next one.                                       *)
    REPEAT CONJ_TAC THEN
    FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN
      UNDISCH_TAC `8 * (k + 1) <= nb` THEN ARITH_TAC);
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* GF(2)-linearity (additivity over word_xor) of the reduction primitives.   *)
(*                                                                           *)
(* Both polyval_reduce_prop3 and ghash_reduce_raw are compositions of        *)
(* GF(2)-linear word operations (word_subword, word_pmul by a constant,      *)
(* word_xor, word_join), hence additive.  These lemmas let the pipelined     *)
(* GHASH Q19 fold distribute the summed-lane hardware reduce over the 8      *)
(* in-flight blocks, so that each block individually matches                 *)
(* GHASH_REDUCE_RAW_KARATSUBA_IS_DOT.                                        *)
(*                                                                           *)
(* Proof recipe: WORD_BITWISE_RULE alone fails because it cannot see into an *)
(* opaque `word_pmul a w`; first distribute the pmuls with WORD_PMUL_XOR     *)
(* (HOL Light Library/words.ml) so that every pmul atom is shared across     *)
(* both sides, then push word_xor into the word_join lanes and split into    *)
(* 64-bit lanes closed by WORD_BITWISE_RULE (pure XOR ring, no bit-blasting  *)
(* of pmul).  A whole-goal WORD_BLAST is not practical (it bit-blasts the    *)
(* pmuls); the lane split is essential.                                      *)
(* ------------------------------------------------------------------------- *)

(* word_xor of two word_joins is the join of the xored lanes (64- and        *)
(* 128-bit-lane variants) + lane-split helpers.                              *)
let JOIN_XOR_LANE = WORD_BLAST
  `word_xor (word_join (a:int64) (b:int64):int128) (word_join c d) =
   word_join (word_xor a c) (word_xor b d)`;;

let JOIN_EQ_LANE = MESON[]
  `(a:int64) = c /\ (b:int64) = d ==> word_join a b:int128 = word_join c d`;;

let JOIN_EQ_128 = MESON[]
  `(a:int128) = c /\ (b:int128) = d ==> word_join a b:int256 = word_join c d`;;

(* polyval_reduce_prop3 distributes over word_xor.                           *)
let PROP3_XOR = prove
 (`!s t:256 word.
     polyval_reduce_prop3 (word_xor s t) =
     word_xor (polyval_reduce_prop3 s) (polyval_reduce_prop3 t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[polyval_reduce_prop3] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_PMUL_XOR; WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[JOIN_XOR_LANE] THEN
  MATCH_MP_TAC JOIN_EQ_LANE THEN CONJ_TAC THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* ghash_reduce_raw is jointly additive in its three arguments.  Proved via  *)
(* the polyval_reduce_g2 bridge (so its two nested pmul layers become a      *)
(* single prop3 of a linear argument) + PROP3_XOR + a 4-lane split.          *)
let GHASH_REDUCE_RAW_XOR = prove
 (`!a1 a2 b1 b2 c1 c2:int128.
     ghash_reduce_raw (word_xor a1 a2) (word_xor b1 b2) (word_xor c1 c2) =
     word_xor (ghash_reduce_raw a1 b1 c1) (ghash_reduce_raw a2 b2 c2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_IS_POLYVAL_G2; POLYVAL_REDUCE_G2] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[GSYM PROP3_XOR] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[JOIN_XOR_256; JOIN_XOR_LANE] THEN
  MATCH_MP_TAC JOIN_EQ_128 THEN CONJ_TAC THEN
  MATCH_MP_TAC JOIN_EQ_LANE THEN CONJ_TAC THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* ------------------------------------------------------------------------- *)
(* Lane-order lemmas: reduce the summed lanes in the exact hardware lane     *)
(* order of the body-end residual.                                           *)
(*                                                                           *)
(* The reassembled body-end reduce is `ghash_reduce_raw P0 P1 P2` where each *)
(* Pl is an 8-term left-associated word_xor sum of per-block Karatsuba       *)
(* pieces, but the three lanes disagree on block order:                      *)
(*      P0 (lo.lo): blocks [1;0;2;3;4;5;6;7], b-lane subword(h^p)(0,64)      *)
(*      P1 (cross): blocks [1;0;3;2;5;4;7;6], b-lane karatsuba_mid(h^p)      *)
(*      P2 (hi.hi): blocks [1;0;2;3;4;5;6;7], b-lane subword(h^p)(64,64)     *)
(* (block j is paired with h-power h^{7-j}).  KARATSUBA_IS_DOT_HW handles    *)
(* the per-block cross-lane form, and REORD_CROSS AC-reorders the cross lane *)
(* [1;0;3;2..] -> [1;0;2;3..] so that the shared-order reduce applies; both  *)
(* are used by GHASH_REDUCE_RAW_DIST8_PLAIN.                                 *)
(* ------------------------------------------------------------------------- *)

(* Per block: the cross lane in the body uses `karatsuba_mid b` and the      *)
(* a-argument subword order (64,64),(0,64); normalise both to the form of    *)
(* GHASH_REDUCE_RAW_KARATSUBA_IS_DOT.                                        *)
let KARATSUBA_IS_DOT_HW = prove
 (`!a b:int128.
    ghash_reduce_raw
      (word_pmul (word_subword a (0,64):int64)
       (word_subword b (0,64):int64):int128)
      (word_pmul
       (word_xor (word_subword a (64,64):int64) (word_subword a (0,64):int64))
                 (karatsuba_mid b):int128)
      (word_pmul (word_subword a (64,64):int64)
       (word_subword b (64,64):int64):int128)
    = polyval_dot a b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[karatsuba_mid] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_subword (a:int128) (64,64):int64) (word_subword a (0,64))
     = word_xor (word_subword a (0,64):int64) (word_subword a (64,64))`] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_KARATSUBA_IS_DOT]);;

(* AC-reorder a left-associated 8-term int128 word_xor from the cross-lane   *)
(* block order [1;0;3;2;5;4;7;6] to the shared order [1;0;2;3;4;5;6;7].      *)
let REORD_CROSS = prove
 (`word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
      (x1:int128) x0) x3) x2) x5) x4) x7) x6 =
   word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
      x1 x0) x2) x3) x4) x5) x6) x7`,
  CONV_TAC WORD_BITWISE_RULE);;

(* The block-0 reduce in the raw swapped-lane form the rem = 2..7 tail arms  *)
(* produce (the accumulator's two 64-bit halves crossed with cb0's: the      *)
(* store-order byteswap):                                                    *)
(*      lo.lo  = word_xor (subword sofar (64,64)) (subword cb0 (0,64))       *)
(*      hi.hi  = word_xor (subword sofar (0,64))  (subword cb0 (64,64))      *)
(*      cross  = word_xor <hi-shape> <lo-shape>                              *)
(* This reduces to polyval_dot (byteswap128 sofar (x) cb0) b.  The block-0   *)
(* accumulator byteswap is absorbed inside this lemma (ABBREV byteswap128    *)
(* sofar, so that the swap-lane rewrites do not re-fire on their own         *)
(* output): a global subword fold cannot be used directly on                 *)
(* those residuals.                                                          *)
let KDOT_B0 = prove
 (`!s c b:int128.
    ghash_reduce_raw
      (word_pmul
       (word_xor (word_subword s (64,64):int64) (word_subword c (0,64):int64))
                 (word_subword b (0,64):int64):int128)
      (word_pmul
       (word_xor (word_xor (word_subword s (0,64):int64)
                  (word_subword c (64,64):int64))
                           (word_xor (word_subword s (64,64):int64)
                            (word_subword c (0,64):int64)))
                 (karatsuba_mid b):int128)
      (word_pmul
       (word_xor (word_subword s (0,64):int64) (word_subword c (64,64):int64))
                 (word_subword b (64,64):int64):int128)
    = polyval_dot (word_xor (byteswap128 s) c) b`,
  REPEAT GEN_TAC THEN ABBREV_TAC `bs = byteswap128 (s:int128)` THEN
  SUBGOAL_THEN
    `word_subword (s:int128) (64,64):int64 = word_subword (bs:int128) (0,64) /\
                word_subword (s:int128) (0,64):int64 =
                  word_subword (bs:int128) (64,64)`
    (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "bs" THEN REWRITE_TAC[byteswap128] THEN CONJ_TAC THEN
    CONV_TAC WORD_BLAST;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN REWRITE_TAC[KARATSUBA_IS_DOT_HW]);;

(* Q19 fold: the 8-block distribution in the body's lane order with all      *)
(* blocks in the clean (non-crossed) form - block order [1;0;2;3;4;5;6;7] on *)
(* lo.lo/hi.hi, [1;0;3;2;5;4;7;6] on the cross lane - reduces to the XOR-sum *)
(* of the eight per-block polyval_dots.  It applies to the body-end Q19      *)
(* residual because the loop invariant states Q19 without a `byteswap128`    *)
(* wrapper (`read Q19 s = nist_ghash..8i`): under that invariant block 0     *)
(* enters the reduce as the ordinary `nist_cipher_block (x) sofar` with no   *)
(* store-order byteswap, so no block-0 crossing (as in KDOT_B0) is needed.   *)
let GHASH_REDUCE_RAW_DIST8_PLAIN = prove
 (`!a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7:int128.
    ghash_reduce_raw
      (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
        (word_pmul (word_subword a1 (0,64):int64)
         (word_subword b1 (0,64):int64):int128)
        (word_pmul (word_subword a0 (0,64):int64)
         (word_subword b0 (0,64):int64):int128))
        (word_pmul (word_subword a2 (0,64):int64)
         (word_subword b2 (0,64):int64):int128))
        (word_pmul (word_subword a3 (0,64):int64)
         (word_subword b3 (0,64):int64):int128))
        (word_pmul (word_subword a4 (0,64):int64)
         (word_subword b4 (0,64):int64):int128))
        (word_pmul (word_subword a5 (0,64):int64)
         (word_subword b5 (0,64):int64):int128))
        (word_pmul (word_subword a6 (0,64):int64)
         (word_subword b6 (0,64):int64):int128))
        (word_pmul (word_subword a7 (0,64):int64)
         (word_subword b7 (0,64):int64):int128))
      (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
        (word_pmul
         (word_xor (word_subword a1 (64,64):int64)
          (word_subword a1 (0,64):int64)) (karatsuba_mid b1):int128)
        (word_pmul
         (word_xor (word_subword a0 (64,64):int64)
          (word_subword a0 (0,64):int64)) (karatsuba_mid b0):int128))
        (word_pmul
         (word_xor (word_subword a3 (64,64):int64)
          (word_subword a3 (0,64):int64)) (karatsuba_mid b3):int128))
        (word_pmul
         (word_xor (word_subword a2 (64,64):int64)
          (word_subword a2 (0,64):int64)) (karatsuba_mid b2):int128))
        (word_pmul
         (word_xor (word_subword a5 (64,64):int64)
          (word_subword a5 (0,64):int64)) (karatsuba_mid b5):int128))
        (word_pmul
         (word_xor (word_subword a4 (64,64):int64)
          (word_subword a4 (0,64):int64)) (karatsuba_mid b4):int128))
        (word_pmul
         (word_xor (word_subword a7 (64,64):int64)
          (word_subword a7 (0,64):int64)) (karatsuba_mid b7):int128))
        (word_pmul
         (word_xor (word_subword a6 (64,64):int64)
          (word_subword a6 (0,64):int64)) (karatsuba_mid b6):int128))
      (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
        (word_pmul (word_subword a1 (64,64):int64)
         (word_subword b1 (64,64):int64):int128)
        (word_pmul (word_subword a0 (64,64):int64)
         (word_subword b0 (64,64):int64):int128))
        (word_pmul (word_subword a2 (64,64):int64)
         (word_subword b2 (64,64):int64):int128))
        (word_pmul (word_subword a3 (64,64):int64)
         (word_subword b3 (64,64):int64):int128))
        (word_pmul (word_subword a4 (64,64):int64)
         (word_subword b4 (64,64):int64):int128))
        (word_pmul (word_subword a5 (64,64):int64)
         (word_subword b5 (64,64):int64):int128))
        (word_pmul (word_subword a6 (64,64):int64)
         (word_subword b6 (64,64):int64):int128))
        (word_pmul (word_subword a7 (64,64):int64)
         (word_subword b7 (64,64):int64):int128))
    = word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
        (polyval_dot a0 b0) (polyval_dot a1 b1)) (polyval_dot a2 b2))
        (polyval_dot a3 b3)) (polyval_dot a4 b4)) (polyval_dot a5 b5))
        (polyval_dot a6 b6)) (polyval_dot a7 b7)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV) [REORD_CROSS] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_XOR] THEN
  REWRITE_TAC[KARATSUBA_IS_DOT_HW] THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* ------------------------------------------------------------------------- *)
(* Q19 GHASH-fold tactic.                                                    *)
(*                                                                           *)
(* Applied to the body-end Q19 residual conjunct                             *)
(*      `<raw ghash reduce of the 8 in-flight ciphertext blocks> =           *)
(*       nist_ghash H tag0 (list_of_seq nist_cipher_block (8i+8))`           *)
(* after splitting it off the raw post-FINAL_STATE conjunction but before    *)
(* the cheap close, whose WORD_SIMPLE_SUBWORD_CONV would destroy the         *)
(* foldable ext/LO structure.  The guarded stepper NSTEP_G_TAC is what keeps *)
(* the accumulator foldable through the 339 body steps.                      *)
(*                                                                           *)
(* Chain:                                                                    *)
(*   1. AC-swap the eor3 top XOR into ghash_reduce_raw's grouping;           *)
(*   2. GSYM ghash_reduce_raw (RECON_GRR);                                   *)
(*   3. reassemble the 8 cipherblocks and distribute the reduce over the 8   *)
(*      clean blocks with GHASH_REDUCE_RAW_DIST8_PLAIN;                      *)
(*   4. fold the RHS nist_ghash to a prop3 chain: NIST_GHASH_IS_POLYVAL +    *)
(*      8(i+1)=SUC^8(8i) + list_of_seq + APPEND + GHASH_ACC_APPEND, then     *)
(*      normalise the CONS SUC-form indices to +n (ADD1; GSYM ADD_ASSOC;     *)
(*      NUM_ADD_CONV) so that the batched ISPECL matches, then               *)
(*      GHASH_POLYVAL_ACC_BATCHED collapses it to the same prop3 sum.        *)
(* ------------------------------------------------------------------------- *)
let RECON_GRR = REWRITE_RULE[LET_DEF; LET_END_DEF] (GSYM ghash_reduce_raw);;

(* MAIN_LOOP_OUT_DISJSPLIT: the 9-way case split of the out-forall bound j < *)
(* 8*((i+1)+1), proved once and used by the body's cheap close for each      *)
(* residual goal.                                                            *)
let MAIN_LOOP_OUT_DISJSPLIT = ARITH_RULE
  `j < 8 * ((i + 1) + 1) <=>
   j < 8 * (i+1) \/ j = 8*(i+1) \/ j = 8*(i+1) + 1 \/
   j = 8*(i+1) + 2 \/ j = 8*(i+1) + 3 \/ j = 8*(i+1) + 4 \/
   j = 8*(i+1) + 5 \/ j = 8*(i+1) + 6 \/ j = 8*(i+1) + 7`;;

(* SETUP_Q30_LANES: the lanes of the SETUP exit counter Q30 = rev32          *)
(* (ctr_block nonce (c+13)).  A whole-term `REWRITE_TAC[ctr_block] THEN      *)
(* WORD_BLAST` on the Q30 word_join would bit-blast the symbolic 96-bit      *)
(* nonce; lane by lane, each 32-bit lane shares the nonce structurally, so   *)
(* WORD_BLAST matches it without blasting.  CTR_BLOCK_RECONSTRUCT_REV32 then *)
(* assembles the full word_reversefields 32 (ctr_block nonce (c+13)).        *)
let SETUP_Q30_LANES = prove
 (`(word_add (word_add
      (word_reversefields 8
        (word_subword (word_reversefields 8 (ctr_block nonce c)) (96,32):int32))
      (word 12)) (word 1):int32 = word (c + 13)) /\
   (word_add (word_reversefields 8
      (word_subword (word_reversefields 8 (ctr_block nonce c)) (64,32):int32))
        (word 0):int32
    = word_subword nonce (0,32)) /\
   (word_add (word_reversefields 8
      (word_subword (word_reversefields 8 (ctr_block nonce c)) (32,32):int32))
        (word 0):int32
    = word_subword nonce (32,32)) /\
   (word_add (word_reversefields 8
      (word_subword (word_reversefields 8 (ctr_block nonce c)) (0,32):int32))
        (word 0):int32
    = word_subword nonce (64,32))`,
  SUBGOAL_THEN
    `word_reversefields 8
       (word_subword (word_reversefields 8 (ctr_block nonce c)) (96,32):int32) =
     word c:int32`
    ASSUME_TAC THENL
   [REWRITE_TAC[ctr_block] THEN
    SPEC_TAC(`word c:int32`,`wc:int32`) THEN GEN_TAC THEN CONV_TAC WORD_BLAST;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [CONV_TAC WORD_RULE;
    REWRITE_TAC[ctr_block] THEN
    SPEC_TAC(`word c:int32`,`wc:int32`) THEN GEN_TAC THEN
    CONV_TAC WORD_BLAST]);;

(* ------------------------------------------------------------------------- *)
(* SETUP final-state reconstruction.                                         *)
(*                                                                           *)
(* After the SETUP drive reaches its exit, ENSURES_FINAL_STATE_TAC +         *)
(* ASM_REWRITE + REWRITE_TAC[htable_mem_8; htable_mem_4] + REPEAT CONJ_TAC   *)
(* split the postcondition, and SETUP_RECON_GEN_TAC (below) dispatches the   *)
(* residual goals by conclusion shape to the closers defined here.           *)
(* ------------------------------------------------------------------------- *)

(* Counter-lane reduction lemmas, shared by CIPHER_CLOSE_TAC and CTR_CLOSE_TAC.
   The counter field of the byte-reversed ctr_block double-reverses to the raw
   counter; the nonce lanes byte-reverse to the nonce sub-lanes.  Proved by
   abstracting `word c` to a fresh word (WORD_BLAST cannot blast `word c`
   for a symbolic num c). *)
let CTR_LANE_LOW = prove
 (`word_reversefields 8
     (word_subword (word_reversefields 8 (ctr_block nonce c)) (96,32):int32) =
   word c`,
  REWRITE_TAC[ctr_block] THEN
  SPEC_TAC(`word c:int32`,`wc:int32`) THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;

let CTR_NONCE_LANES = prove
 (`(word_subword (word_reversefields 8 (ctr_block nonce c)) (64,32):int32 =
    word_reversefields 8 (word_subword nonce (0,32))) /\
   (word_subword (word_reversefields 8 (ctr_block nonce c)) (32,32):int32 =
    word_reversefields 8 (word_subword nonce (32,32))) /\
   (word_subword (word_reversefields 8 (ctr_block nonce c)) (0,32):int32 =
    word_reversefields 8 (word_subword nonce (64,32)))`,
  REWRITE_TAC[ctr_block] THEN
  SPEC_TAC(`word c:int32`,`wc:int32`) THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* CIPHER_ID_TAC: the AES-input identity residual for block j (j = 1..7):
        word_xor (RF8 (cipher (RF8 <KS_j>) rk)) (inblock j) =
        word_xor (RF8 (cipher (ctr_block nonce (c+j)) rk)) (inblock j)
   where <KS_j> is the counter block SETUP builds with add/rev32.  Peel the
   outer word_xor (-) (inblock j), RF8 and cipher (-) rk by
   AP_THM/AP_TERM, leaving RF8 <KS_j> = ctr_block nonce (c+j), which
   ctr_block + WORD_BLAST closes directly: on the fully typed goal the
   symbolic 96-bit nonce appears identically on both sides, so WORD_BLAST
   does not blast it. *)
let CIPHER_ID_TAC =
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST;;

(* CTR_CLOSE_TAC: Q0..Q4 (rev8) + Q30 (rev32) fresh-counter reconstruction.
   Reduce each lane to the CTR_BLOCK_RECONSTRUCT_REV8/REV32 pattern
   (SETUP_Q30_LANES for Q30; CTR_LANE_LOW + double-RF8 cancel +
   CTR_NONCE_LANES for Q0..Q4), combine the counter add (GSYM WORD_ADD),
   fold to ctr_block, then peel and close the counter-index equality by
   ARITH.  No whole-term WORD_BLAST: it would have to bit-blast the 128-bit
   counter term. *)
let CTR_CLOSE_TAC =
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SETUP_Q30_LANES; CTR_LANE_LOW] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[CTR_NONCE_LANES] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8; CTR_BLOCK_RECONSTRUCT_REV32] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;;

(* FLAG_CLOSE_GEN_TAC: the prepretail-check flag conjunct                    *)
(* ((NF<=>VF)<=>(0=k)) at i = 0.  BRIDGE_GE turns it into a signed compare,  *)
(* SETUP_X5_END_GEN rewrites the raw round-down X5 pointer to end_p, and     *)
(* SETUP_GE_FALSE_2 (k >= 1) discharges the compare.                         *)
let FLAG_CLOSE_GEN_TAC =
  REWRITE_TAC[BRIDGE_GE] THEN
  SUBGOAL_THEN
    `word_add (word_and (word_sub (word ((128 * nb) DIV 8):int64) (word 1))
                        (word 18446744073709551488)) in_p =
     word_add in_p (word (128 * (k + 1)))`
    SUBST1_TAC THENL
   [MATCH_MP_TAC SETUP_X5_END_GEN THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[MATCH_MP SETUP_GE_FALSE_2
      (CONJ (ASSUME `~(k = 0)`)
            (ASSUME `val(in_p:int64) + 128 * (k + 1) < 2 EXP 63`))]];;

(* Extended-guard stepper for the drain.  NSTEP_G_TAC protects Q17/Q18/Q19   *)
(* from the per-step WORD_SIMPLE_SUBWORD_CONV; the drain also needs Q20/Q21  *)
(* protected, because its reduce takes ext(v18) -> Q21 and pmull(v18) -> Q17 *)
(* at different steps (0xe9c and 0xe64): if Q21's subwords were collapsed,   *)
(* the two copies of the mid-accumulator v18 would differ and RECON_GRR      *)
(* could not match.                                                          *)
let is_ghash_acc_pp th =
  let c = concl th in
  can (find_term (fun t -> match t with
      Comb(Const("read",_), r) ->
        (match r with
         | Const("Q17",_) | Const("Q18",_) | Const("Q19",_)
         | Const("Q20",_) | Const("Q21",_) -> true
         | _ -> false)
    | _ -> false)) c;;

(* The word_add-nest flatten of NSTEP_GP_TAC (the same rewrite as            *)
(* WB_WADD_RULE).                                                            *)
let NSTEP_GP_WADD_RULE = REWRITE_RULE[WORD_RULE
  `word_add (word_add b (word m)) (word nn):int64 = word_add b (word(m+nn))`];;

(* Q30 counter closer (the drain does three `add v30`, so the exit counter   *)
(* is 8*k+c+16).                                                             *)
let PP_CTR_CLOSE_TAC =
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV32] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;;

(* Store-permutation lemmas: TAG_STORE_REV64 is the `ext v19,#8` + `rev64    *)
(* v19` byte permutation the tail applies before `st1 {v19},[x3]`, equal to  *)
(* word_reversefields 8; IVEC_STORE_REV32 is the rev32 v30 permutation       *)
(* before `str q30,[x16]`.  Both by BITBLAST.                                *)
let TAG_STORE_REV64 = prove
 (`!x:int128.
    word_join
     (word_join
      (word_join
       (word_join (word_subword x (0,8):byte) (word_subword x (8,8):byte):int16)
       (word_join (word_subword x (16,8):byte)
        (word_subword x (24,8):byte):int16):int32)
      (word_join
       (word_join (word_subword x (32,8):byte)
        (word_subword x (40,8):byte):int16)
       (word_join (word_subword x (48,8):byte)
        (word_subword x (56,8):byte):int16):int32):int64)
     (word_join
      (word_join
       (word_join (word_subword x (64,8):byte)
        (word_subword x (72,8):byte):int16)
       (word_join (word_subword x (80,8):byte)
        (word_subword x (88,8):byte):int16):int32)
      (word_join
       (word_join (word_subword x (96,8):byte)
        (word_subword x (104,8):byte):int16)
       (word_join (word_subword x (112,8):byte)
        (word_subword x (120,8):byte):int16):int32):int64):int128
    = word_reversefields 8 x`,
  CONV_TAC BITBLAST_RULE);;

(* The small paths (FAST1..FAST4) end in the shared L256_enc_small_reduce,   *)
(* which replaces the `ext v19,#8; rev64 v19` byte reverse with a single     *)
(* `tbl v19.16b,{v19.16b},v12.16b` (at 0x18dc), v12 holding the reverse      *)
(* index word 0x000102030405060708090a0b0c0d0e0f.  arm_TBL (datasize 128)    *)
(* yields `usimd16 (\x. word_subword Q19 (8*val x,8)) Q12`; with that index  *)
(* in Q12 this equals word_reversefields 8 Q19, so these tails close with    *)
(* TAG_STORE_REV64 like the ext+rev64 path.                                  *)

let IVEC_STORE_REV32 = prove
 (`!y:int128.
    word_join
     (word_join
      (word_reversefields 8
       (word_subword (word_reversefields 32 y) (96,32):int32):int32)
      (word_reversefields 8
       (word_subword (word_reversefields 32 y) (64,32):int32):int32):int64)
     (word_join
      (word_reversefields 8
       (word_subword (word_reversefields 32 y) (32,32):int32):int32)
      (word_reversefields 8
       (word_subword (word_reversefields 32 y)
        (0,32):int32):int32):int64):int128
    = word_reversefields 8 y`,
  CONV_TAC BITBLAST_RULE);;

(* KS_SOLVE inverts a keystream fact `word_xor (read Qj s) rkn = ks` into    *)
(* `read Qj s = word_xor ks rkn`, so that the ciphertext eor3 outputs are    *)
(* state-independent.                                                        *)
let KS_SOLVE = prove
 (`!a b c:int128. word_xor a b = c ==> a = word_xor c b`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  CONV_TAC WORD_BITWISE_RULE);;

let DISCARD_REGS_TAC deadl : tactic =
  let reg_of th =
    try let c = concl th in
        if not(is_eq c) then "" else
        let f,args = strip_comb (lhs c) in
        if fst(dest_const f) = "read"
        then (match args with c::_ ->
              (try fst(dest_const c) with Failure _ -> "") | _ -> "")
        else ""
    with Failure _ -> "" in
  REPEAT(FIRST_X_ASSUM(fun th ->
    if List.mem (reg_of th) deadl then K ALL_TAC th else fail()));;

(* DISCARD_DEAD_REDUCE_SCRATCH_TAC, used in each tail arm right after the    *)
(* Q19 fold, drops the Q-registers that are dead from there on: every        *)
(* register except Q0..Q7 (the keystreams), Q19 (the folded tag) and Q30     *)
(* (the ivec counter) is neither read by the remaining ext/rev64/st1 steps   *)
(* nor mentioned by the postcondition or the frame, so ARM_STEPS_TAC need    *)
(* not re-stamp their large terms.  The list has 19 registers (Q8..Q18,      *)
(* Q20..Q26, Q29); Q27, Q28 and Q31 are not in it (TAIL_REM8 drops them      *)
(* separately where they die).                                               *)
let DISCARD_DEAD_REDUCE_SCRATCH_TAC : tactic =
  DISCARD_REGS_TAC
    ["Q17"; "Q18"; "Q20"; "Q21"; "Q22"; "Q23"; "Q24"; "Q25"; "Q26";
     "Q29"; "Q16"; "Q8"; "Q9"; "Q10"; "Q11"; "Q12";
     "Q13"; "Q14"; "Q15"];;

(* DISCARD_DEAD_KEYMEM_TAC drops the round-key memory facts `read (memory :> *)
(* bytes128 (word_add key_p (word (16*i)))) s = word_reversefields 8 (EL i   *)
(* rk)`, i = 0..nr, which DISCARD_REGS_TAC does not touch (its reg_of        *)
(* returns "" for a `memory :> ..` component).  The tail runs no AES rounds: *)
(* the keystreams Q0..Q7 are already computed at entry (the precondition's   *)
(* `word_xor (read Qj) rkn = word_reversefields 8 (cipher ..)`), no          *)
(* instruction in 0xee0..0x14e0 uses x11, and neither the postcondition nor  *)
(* the frame mentions key_p memory.  TAIL_REM8 drops these facts right after *)
(* the 9-step prefix, so that they are not carried through the rest of the   *)
(* drive.                                                                    *)
let DISCARD_DEAD_KEYMEM_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c &&
       can (find_term (fun t -> t = `key_p:int64`)) (lhs c) &&
       can (find_term
            (fun t -> match t with Const("memory",_) -> true | _ -> false))
           (lhs c)
    then K ALL_TAC th else fail()));;

(* DISCARD_DEAD_HTABLE_TAC drops the six htable facts at offsets 96..176     *)
(* (byteswap128 (h_power h 4..7) and the karatsuba_mid pairs for h_power     *)
(* 4..7) of the 12 that htable_mem_8 contributes (offsets 0, 16, .., 176).   *)
(* The 9-step tail prefix loads those offsets into q20..q25 (the ldps at     *)
(* 0xee0/0xeec/0xef4); after it no instruction reads them (the drains reload *)
(* only offsets 0..80) and the postcondition mentions no htable memory, so   *)
(* TAIL_REM8 drops them right after the prefix.  DISCARD_DEAD_KEYMEM_TAC and *)
(* DISCARD_REGS_TAC miss them (one keys on key_p, the other on               *)
(* register components).                                                     *)
let dead_htable_offs = [96; 112; 128; 144; 160; 176];;
let DISCARD_DEAD_HTABLE_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c &&
       can (find_term (fun t -> t = `htable_p:int64`)) (lhs c) &&
       can (find_term
            (fun t -> match t with Const("memory",_) -> true | _ -> false))
           (lhs c) &&
       can (find_term (fun t -> match t with
              Comb(Const("word",_), n) ->
                (try List.mem (dest_small_numeral n) dead_htable_offs
                 with Failure _ -> false)
            | _ -> false)) (lhs c)
    then K ALL_TAC th else fail()));;

let TAIL_X5_REM1 = prove
 (`!(in_p:int64) g.
     word_sub (word_add in_p (word (16 * (8 * g + 1))))
              (word_add in_p (word (128 * g))) = word 16:int64`,
  REPEAT STRIP_TAC THEN CONV_TAC WORD_RULE);;

(* Single-block Q19 fold (the front end is shared with TAIL_Q19_FOLD_G_TAC,  *)
(* with a single-block APPEND instead of GHASH_POLYVAL_ACC_BATCHED).  Proves *)
(* that the raw single-block ghash_reduce at s82 equals the compact          *)
(* nist_ghash..(8*g+1): RECON_GRR exposes ghash_reduce_raw, the block        *)
(* normalises to nist_cipher_block(8*g), KARATSUBA_IS_DOT_HW collapses the   *)
(* three Karatsuba pmulls to a single polyval_dot, and the one-element       *)
(* list_of_seq(SUC)/NIST_GHASH_APPEND/CONS + NIST_DOT_IS_POLYVAL_DOT +       *)
(* h_power 0 closes it.                                                      *)
let TAIL_Q19_FOLD_REM1_TAC =
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (word_xor (i:int128) (word_xor a r)) r = word_xor i a`] THEN
  REWRITE_TAC[RECON_GRR] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV WORD_REDUCE_CONV)) THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE `word_xor (word 0:int128) x = x`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (i:int128) (word_reversefields 8 a) =
       word_xor (word_reversefields 8 a) i`] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN
  REWRITE_TAC[GSYM cipher_block] THEN REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[KARATSUBA_IS_DOT_HW] THEN
  REWRITE_TAC[ARITH_RULE `8 * g + 1 = SUC(8 * g)`;
              ARITH_RULE `1 + 8 * g = SUC(8 * g)`] THEN
  REWRITE_TAC[list_of_seq] THEN
  REWRITE_TAC[NIST_GHASH_APPEND] THEN
  REWRITE_TAC[NIST_GHASH_CONS; nist_ghash] THEN
  REWRITE_TAC[NIST_DOT_IS_POLYVAL_DOT] THEN
  REWRITE_TAC[CONJUNCT1 h_power];;

(* x5 at the rem = 2 tail entry: 16*nb - 128*g = 32 for nb = 8*g+2; once it  *)
(* is rewritten to `word 32` the cascade resolves to the rem = 2 arm (b.eq   *)
(* at 0x142c -> 0x1434) with concrete flags.                                 *)
let TAIL_X5_REM2 = prove
 (`!(in_p:int64) g.
     word_sub (word_add in_p (word (16 * (8 * g + 2))))
              (word_add in_p (word (128 * g))) = word 32:int64`,
  REPEAT STRIP_TAC THEN CONV_TAC WORD_RULE);;

let TAIL_X5_REM3 = prove
 (`!(in_p:int64) g.
     word_sub (word_add in_p (word (16 * (8 * g + 3))))
              (word_add in_p (word (128 * g))) = word 48:int64`,
  REPEAT STRIP_TAC THEN CONV_TAC WORD_RULE);;

let TAIL_X5_REM4 = prove
 (`!(in_p:int64) g.
     word_sub (word_add in_p (word (16 * (8 * g + 4))))
              (word_add in_p (word (128 * g))) = word 64:int64`,
  REPEAT STRIP_TAC THEN CONV_TAC WORD_RULE);;

let TAIL_X5_REM5 = prove
 (`!(in_p:int64) g.
     word_sub (word_add in_p (word (16 * (8 * g + 5))))
              (word_add in_p (word (128 * g))) = word 80:int64`,
  REPEAT STRIP_TAC THEN CONV_TAC WORD_RULE);;

let TAIL_X5_REM6 = prove
 (`!(in_p:int64) g.
     word_sub (word_add in_p (word (16 * (8 * g + 6))))
              (word_add in_p (word (128 * g))) = word 96:int64`,
  REPEAT STRIP_TAC THEN CONV_TAC WORD_RULE);;

let TAIL_X5_REM7 = prove
 (`!(in_p:int64) g.
     word_sub (word_add in_p (word (16 * (8 * g + 7))))
              (word_add in_p (word (128 * g))) = word 112:int64`,
  REPEAT STRIP_TAC THEN CONV_TAC WORD_RULE);;

let TAIL_X5_128_G = prove
 (`!(in_p:int64) nb g.
     8 * g + 8 = nb
     ==> word_sub (word_add in_p (word (16 * nb)))
                  (word_add in_p (word (128 * g))) = word 128:int64`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  CONV_TAC WORD_RULE);;

(* Helper for the TAIL leg's existential precondition: an ensures with an    *)
(* existential precondition follows from the ensures for every witness (from *)
(* the definition of ensures: the precondition ?v w. P is stripped and the   *)
(* witnesses specialise the hypothesis).  Two-existential form, matching the *)
(* 0xee0 mid-state.                                                          *)
let ENSURES_EXISTS2_PRECONDITION = prove
 (`!step (P:B->C->A->bool) Q Fr.
        (!v w. ensures step (\s. P v w s) Q Fr)
        ==> ensures step (\s. ?v w. P v w s) Q Fr`,
  REWRITE_TAC[ensures] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`v:B`; `w:C`]) THEN
  DISCH_THEN(MP_TAC o SPEC `s:A`) THEN ASM_REWRITE_TAC[]);;

(* WB_X9_NORM: the prologue's `lsr x9,x1,#3` gives word ((128*nb) DIV 8)     *)
(* when X1 = word (128*nb) and 128*nb < 2^64.                                *)
let WB_X9_NORM = prove
 (`128 * nb < 2 EXP 64
   ==> word_ushr (word (128 * nb):int64) 3 = word ((128 * nb) DIV 8)`,
  STRIP_TAC THEN REWRITE_TAC[word_ushr] THEN AP_TERM_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 3 = 8`] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* loop_count = 0 branch mechanics (nb in 1..8).                             *)
(* ------------------------------------------------------------------------- *)

(* When groups = (nb-1) DIV 8 = 0 (i.e. nb <= 8), the round-down end pointer *)
(* x5 = in_p + ((16*nb - 1) AND ~0x7f) collapses to in_p, because 16*nb-1 <= *)
(* 127 < 128 = 2^7, so masking off the low 7 bits gives 0.  Then `cmp x0,x5; *)
(* b.ge` at 0x44c (x0 = in_p) is taken, skipping the main loop and going     *)
(* straight to the tail cascade at pc+0xee0.  These two lemmas are the       *)
(* analogues of SETUP_BRANCH_COND_FALSE_GEN / SETUP_X5_END_GEN for the       *)
(* groups = 0 leg: there the branch falls through (groups >= 1), here it     *)
(* is taken.                                                                 *)

(* x5 (the rounded-down last-full-group pointer) = in_p for nb in 1..8. *)
let WB_X5_GROUPS0 = prove
 (`!(in_p:int64) nb.
     1 <= nb /\ nb <= 8
     ==> word_add
           (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                     (word 18446744073709551488))
           in_p = in_p`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 16 * nb` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word (16 * nb)) (word 1):int64 = word (16 * nb - 1)`
    SUBST1_TAC THENL
   [REWRITE_TAC[WORD_SUB] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word 18446744073709551488:int64 = word_not (word (2 EXP 7 - 1))`
    SUBST1_TAC THENL
   [CONV_TAC(RAND_CONV(RAND_CONV(RAND_CONV NUM_REDUCE_CONV))) THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[WORD_AND_NOT_MASK_WORD] THEN
  SUBGOAL_THEN `val(word (16 * nb - 1):int64) DIV 2 EXP 7 = 0` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_LT THEN
    SUBGOAL_THEN `val(word (16 * nb - 1):int64) = 16 * nb - 1` SUBST1_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC];
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0]]);;

(* The b.ge at 0x44c condition (the exact NF<>VF biconditional the stepper   *)
(* emits for `cmp x0,x5` with x0 = in_p) collapses to T for nb in 1..8, so   *)
(* the conditional PC resolves to the tail entry pc+0xee0.                   *)
let WB_BRANCH_COND_TRUE = prove
 (`!(in_p:int64) nb.
     1 <= nb /\ nb <= 8
     ==> ((ival (word_sub in_p
                  (word_add
                    (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                              (word 18446744073709551488))
                    in_p)) < &0 <=>
           ~(ival in_p -
             ival (word_add
                    (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                              (word 18446744073709551488))
                    in_p) =
             ival (word_sub in_p
                    (word_add
                      (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                                (word 18446744073709551488))
                      in_p)))) <=> T)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WB_X5_GROUPS0] THEN
  REWRITE_TAC[WORD_SUB_REFL; INT_SUB_REFL; IVAL_WORD_0] THEN
  INT_ARITH_TAC);;

(* SETUP_Q30_LANES_10: the lanes of the SETUP0 exit counter Q30 = ctr_block  *)
(* nonce (c+8) (base c, +7 at 0x94, then +1 at 0xc4); cf. SETUP_Q30_LANES    *)
(* for c+13.                                                                 *)
let SETUP_Q30_LANES_10 = prove
 (`(word_add (word_add
      (word_reversefields 8
        (word_subword (word_reversefields 8 (ctr_block nonce c)) (96,32):int32))
      (word 7)) (word 1):int32 = word (c + 8)) /\
   (word_add (word_reversefields 8
      (word_subword (word_reversefields 8 (ctr_block nonce c)) (64,32):int32))
        (word 0):int32
    = word_subword nonce (0,32)) /\
   (word_add (word_reversefields 8
      (word_subword (word_reversefields 8 (ctr_block nonce c)) (32,32):int32))
        (word 0):int32
    = word_subword nonce (32,32)) /\
   (word_add (word_reversefields 8
      (word_subword (word_reversefields 8 (ctr_block nonce c)) (0,32):int32))
        (word 0):int32
    = word_subword nonce (64,32))`,
  SUBGOAL_THEN
    `word_reversefields 8
       (word_subword (word_reversefields 8 (ctr_block nonce c)) (96,32):int32) =
     word c:int32`
    ASSUME_TAC THENL
   [REWRITE_TAC[ctr_block] THEN
    SPEC_TAC(`word c:int32`,`wc:int32`) THEN GEN_TAC THEN CONV_TAC WORD_BLAST;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [CONV_TAC WORD_RULE;
    REWRITE_TAC[ctr_block] THEN
    SPEC_TAC(`word c:int32`,`wc:int32`) THEN GEN_TAC THEN
    CONV_TAC WORD_BLAST]);;

(* Q30 counter closer (the next counter, index c+8): CTR_CLOSE_TAC with the lane
   lemma SETUP_Q30_LANES_10 in place of SETUP_Q30_LANES.  Reconstruct the
   counter lanes structurally, then peel and close the counter-index
   equality by ARITH; a whole-term WORD_BLAST would bit-blast the 128-bit
   counter term. *)
let SETUP0_CTR_CLOSE_TAC =
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SETUP_Q30_LANES_10; CTR_LANE_LOW] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[CTR_NONCE_LANES] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8; CTR_BLOCK_RECONSTRUCT_REV32] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;;

(* Q19 init closer: nist_ghash over the empty list = tag0.                   *)
let SETUP0_Q19_CLOSE_TAC =
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[list_of_seq; NIST_GHASH_NIL] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_BLAST;;

(* Entry-guard lemmas for nb >= 1: WB_GUARD1_NONZERO_GEN (`cbz x1` does not  *)
(* branch: word (128*nb) is nonzero) and WB_GUARD2_MASK_GEN (`tst x1,#0x7f`  *)
(* gives 0: 128 divides 128*nb).                                             *)
let WB_GUARD1_NONZERO_GEN = prove
 (`!nb. 1 <= nb /\ 128 * nb < 2 EXP 64
        ==> ~(word (128 * nb):int64 = word 0) /\
            ~(val(word (128 * nb):int64) = 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ_0] THEN
  SUBGOAL_THEN `val(word(128 * nb):int64) = 128 * nb` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let WB_GUARD2_MASK_GEN = prove
 (`!nb. 1 <= nb /\ 128 * nb < 2 EXP 64
        ==> word_and (word (128 * nb):int64) (word 0x7f) = word 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `0x7f = 2 EXP 7 - 1`; WORD_AND_MASK_WORD] THEN
  SUBGOAL_THEN `val(word(128 * nb):int64) = 128 * nb` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    AP_TERM_TAC THEN REWRITE_TAC[ARITH_RULE `2 EXP 7 = 128`] THEN
    MP_TAC(SPECL [`128`; `nb:num`] MOD_MULT) THEN ARITH_TAC]);;
