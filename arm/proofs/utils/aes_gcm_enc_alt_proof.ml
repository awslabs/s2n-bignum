(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The proof of the 8-way AES-GCM encrypt kernels aes128_gcm_enc_alt and     *)
(* aes256_gcm_enc_alt, written once for both key sizes.  The AES-128 kernel  *)
(* is the AES-256 one with 10 rounds and 11 round keys instead of 14 and 15, *)
(* so the two proofs differ only in the cipher, the code, the number of      *)
(* rounds and some program counters and step counts.                         *)
(*                                                                           *)
(* This file is not loaded with needs.  Each kernel proof defines its        *)
(* machine code, binds enc_alt_kernel (of type aes_gcm_enc_alt_kernel, in    *)
(* arm/proofs/utils/aes_gcm_enc_alt_common.ml) to its parameters, loads this *)
(* file with loadt and then writes out its exported theorems, which are      *)
(* proved here.  Theorem names drop the key size: AES_GCM_ENC_ALT_TAIL_REM   *)
(* here is AES128_GCM_ENC_ALT_TAIL_REM in the AES-128 proof.  The quotations *)
(* that depend on the kernel are wrapped in kterm, which instantiates their  *)
(* free variables: cipher (the AES cipher), tmc (the code without the BTI    *)
(* landing pad), nr (the number of rounds, so that EL nr rk, written rkn in  *)
(* the comments, is the last round key), nrk (the number of round keys),     *)
(* keybytes (the size of the key schedule), the program counters pc_loop,    *)
(* pc_backedge, pc_prepretail, pc_tail, pc_end and pc_fast1..pc_fast4, and   *)
(* the states sfast1..sfast4 at the last four.  The step counts that differ  *)
(* are OCaml integers (setup_tail_branch, loop_ldp1, loop_ldp2,              *)
(* loop_backedge, prepretail_steps, fast1_steps..fast4_steps).  Addresses,   *)
(* labels and step numbers in the comments are those of the AES-256 kernel.  *)
(*                                                                           *)
(* Proof structure (offsets of the -DNO_IBT code).  The core theorem         *)
(* AES_GCM_ENC_ALT_CORRECT, pc+0x38 (after the prologue) to pc+pc_end        *)
(* (L*_enc_epilogue), for nb >= 1, is assembled from legs by block count:    *)
(*                                                                           *)
(* - nb <= 4: FAST1..FAST4, the small path (b.le L*_enc_small at pc+0x50);   *)
(* - 5 <= nb <= 8: SETUP0 (pc+0x38 -> pc+pc_tail), then TAIL_REM;            *)
(* - 9 <= nb <= 16: SETUP_G1 (pc+0x38 -> pc+pc_prepretail), PREPRETAIL_GEN   *)
(*   (pc+pc_prepretail -> pc+pc_tail), then TAIL_REM;                        *)
(* - nb >= 17: SETUP_GEN (pc+0x38 -> pc+pc_loop), MAIN_LOOP (pc+pc_loop ->   *)
(*   pc+pc_prepretail, k = (nb-1) DIV 8 - 1 iterations), PREPRETAIL_GEN,     *)
(*   then TAIL_REM.                                                          *)
(*                                                                           *)
(* TAIL_REM (pc+pc_tail -> pc+pc_end) does the last 1..8 blocks through the  *)
(* arms TAIL_REM1..TAIL_REM8.  AES_GCM_ENC_ALT_NOIBT_SUBROUTINE_CORRECT adds *)
(* the length guards, the prologue and the epilogue; the _SAFE theorems      *)
(* prove constant-time and memory safety along the same structure.           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The kernel's parameters.                                                  *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_ENC_ALT_EXEC = enc_alt_kernel.eak_exec;;
let KEY_SPLIT = enc_alt_kernel.eak_key_split;;
let CIPHER_KEYLIST = enc_alt_kernel.eak_cipher_keylist;;
let CIPHER_RECONSTRUCT = enc_alt_kernel.eak_cipher_reconstruct;;
let XOR_CIPHER_RECONSTRUCT = enc_alt_kernel.eak_xor_cipher_reconstruct;;
let aes_gcm_enc_alt_name = enc_alt_kernel.eak_name;;
let setup_tail_branch = enc_alt_kernel.eak_setup_tail_branch;;
let loop_ldp1,loop_ldp2 = enc_alt_kernel.eak_loop_ldp;;
let loop_backedge = enc_alt_kernel.eak_loop_backedge;;
let prepretail_steps = enc_alt_kernel.eak_prepretail_steps;;
let fast1_steps,fast2_steps,fast3_steps,fast4_steps =
  enc_alt_kernel.eak_fast_steps;;

let enc_alt_saved_implicit_types = !the_implicit_types;;

the_implicit_types :=
 ["cipher",`:int128->int128 list->int128`; "tmc",`:byte list`;
  "nr",`:num`; "nrk",`:num`; "keybytes",`:num`;
  "pc_loop",`:num`; "pc_backedge",`:num`; "pc_prepretail",`:num`;
  "pc_tail",`:num`; "pc_end",`:num`;
  "pc_fast1",`:num`; "pc_fast2",`:num`; "pc_fast3",`:num`; "pc_fast4",`:num`;
  "sfast1",`:armstate`; "sfast2",`:armstate`; "sfast3",`:armstate`;
  "sfast4",`:armstate`] @ !the_implicit_types;;

let kterm =
  let k = enc_alt_kernel in
  let n = mk_small_numeral
  and s i = mk_var("s"^string_of_int i,`:armstate`) in
  let p1,p2,p3,p4 = k.eak_pc_fast and f1,f2,f3,f4 = k.eak_fast_steps in
  vsubst
   [k.eak_cipher,`cipher:int128->int128 list->int128`;
    k.eak_tmc,`tmc:byte list`;
    n k.eak_rounds,`nr:num`;
    n(k.eak_rounds + 1),`nrk:num`;
    n(16 * (k.eak_rounds + 1)),`keybytes:num`;
    n k.eak_pc_loop,`pc_loop:num`;
    n k.eak_pc_backedge,`pc_backedge:num`;
    n k.eak_pc_prepretail,`pc_prepretail:num`;
    n k.eak_pc_tail,`pc_tail:num`;
    n k.eak_pc_end,`pc_end:num`;
    n p1,`pc_fast1:num`; n p2,`pc_fast2:num`;
    n p3,`pc_fast3:num`; n p4,`pc_fast4:num`;
    s f1,`sfast1:armstate`; s f2,`sfast2:armstate`;
    s f3,`sfast3:armstate`; s f4,`sfast4:armstate`];;

(* NSTEP steps one instruction and then applies the word_add flatten,        *)
(* NORMOFF_RULE and SUBWORD_NORM_RULE to every assumption in a single        *)
(* RULE_ASSUM_TAC pass.  It has no is_ghash_acc guard: it is used where no   *)
(* large GHASH accumulator is live (the setup legs and the dispatch and AES  *)
(* part of FAST1..FAST4).                                                    *)
let NSTEP n =
  ARM_STEPS_TAC AES_GCM_ENC_ALT_EXEC [n] THEN
  RULE_ASSUM_TAC(fun th -> SUBWORD_NORM_RULE (NORMOFF_RULE (WB_WADD_RULE th)));;

let NSTEP_G n =
  ARM_STEPS_TAC AES_GCM_ENC_ALT_EXEC [n] THEN
  RULE_ASSUM_TAC(fun th ->
    if is_ghash_acc th then th
    else SUBWORD_NORM_RULE (NORMOFF_RULE (WB_WADD_RULE th)));;

let LDP_STEP4_TAC n =
  let sprev = "s"^string_of_int (n-1) in
  let sn = "s"^string_of_int n in
  INBLOCKS_TAC sprev THEN
  ARM_VERBOSE_STEP_TAC AES_GCM_ENC_ALT_EXEC sn THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_add b (word m)) (word nn):int64 = word_add b (word(m+nn))`]) THEN
  RULE_ASSUM_TAC NORMOFF_RULE THEN
  (fun (asl,w as gl) ->
     let memfacts = filter is_inp_memfact (map snd asl) in
     RULE_ASSUM_TAC(REWRITE_RULE memfacts) gl) THEN
  RULE_ASSUM_TAC SUBWORD_NORM_RULE THEN
  DISCARD_OLDSTATE_TAC sn;;

let LDP_SETUP_TAC n =
  let sprev = "s"^string_of_int (n-1) in
  let sn = "s"^string_of_int n in
  SETUP_INBLOCKS_TAC sprev THEN
  ARM_VERBOSE_STEP_TAC AES_GCM_ENC_ALT_EXEC sn THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_add b (word m)) (word nn):int64 = word_add b (word(m+nn))`]) THEN
  RULE_ASSUM_TAC NORMOFF_RULE THEN
  (fun (asl,w as gl) ->
     (* Normalise the setup input memfacts so that their addresses match the *)
     (* ldp reads: reduce `16*j` to a literal (NUM_MULT_CONV) and collapse   *)
     (* `word_add in_p (word 0)` to in_p (WORD_ADD_0).  Without this the     *)
     (* block-0 ldp read (at the bare in_p) does not match                   *)
     (* SETUP_INBLOCKS_TAC's address `word_add in_p (word (16*0))`, so that  *)
     (* load stays opaque (`read Q8 s = read(memory:>bytes128 in_p) s_prev`) *)
     (* and DISCARD_OLDSTATE drops the register fact.                        *)
     let norm th =
       REWRITE_RULE[WORD_ADD_0]
         (try CONV_RULE(TOP_DEPTH_CONV NUM_MULT_CONV) th with _ -> th) in
     let memfacts = map norm (filter is_inp_memfact (map snd asl)) in
     RULE_ASSUM_TAC(REWRITE_RULE memfacts) gl) THEN
  RULE_ASSUM_TAC SUBWORD_NORM_RULE THEN
  DISCARD_OLDSTATE_TAC sn;;

(* The part of the setup from its first guard to its second, which is the    *)
(* same code in both kernels: after the b.ge L*_enc_tail at step             *)
(* setup_tail_branch come the four ldps of the first input group (1, 2, 10   *)
(* and 11 steps later) and the b.ge L*_enc_prepretail (28 steps later).      *)
let SETUP_LOADS_TAC =
  let b = setup_tail_branch in
  LDP_SETUP_TAC (b + 1) THEN LDP_SETUP_TAC (b + 2) THEN
  MAP_EVERY NSTEP ((b + 3)--(b + 9)) THEN
  LDP_SETUP_TAC (b + 10) THEN LDP_SETUP_TAC (b + 11) THEN
  MAP_EVERY NSTEP ((b + 12)--(b + 27)) THEN
  NSTEP (b + 28);;

(* The invariant states the Q19 accumulator plain, not wrapped in a          *)
(* `byteswap128`: read Q19 s = nist_ghash..8i, rather than read Q19 s =      *)
(* byteswap128(nist_ghash..8i).  This kernel's main-loop body has only a     *)
(* leading `ext v19` (at 0x4f4) and no trailing ext (byteswap parity 0).     *)
(* With the plain invariant the body-end reduce (parity 0) matches the plain *)
(* RHS (parity 0) and the fold closes via the flat 8-`polyval_dot`-sum       *)
(* route; a byteswap-wrapped invariant (parity 1) could not, since byteswap  *)
(* identities only move the wrapper from side to side.  Block 0 enters the   *)
(* reduce as the ordinary clean `nist_cipher_block (x) sofar` (no            *)
(* store-order byteswap), so the fold uses GHASH_REDUCE_RAW_DIST8_PLAIN (all *)
(* blocks clean).                                                            *)
let Q19_FOLD_TAC =
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (x:int128) e) p = word_xor (word_xor x p) e`] THEN
  REWRITE_TAC[RECON_GRR] THEN
  (* Reassemble the 8 cipherblocks (the plain invariant leaves no            *)
  (* store-order byteswap on the accumulator to cancel).                     *)
  REWRITE_TAC[GSYM cipher_block] THEN REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  (* Re-fold the block-accumulator's distributed subwords (subword X (x)     *)
  (* subword Y -> subword(X (x) Y)) so that DIST8_PLAIN's lo.lo/hi.hi lanes  *)
  (* match, then distribute the reduce over the 8 clean blocks.              *)
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_DIST8_PLAIN] THEN
  (* RHS: fold nist_ghash..8(i+1) to prop3(pmul chain), plain, no byteswap. *)
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE
    `8 * (i + 1) = SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(8 * i))))))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  MP_TAC(ISPECL
    [kterm `ghash_twist (cipher (word 0) rk)`;
     kterm `[nist_cipher_block cipher c nonce rk inblock (8*i+1);
       nist_cipher_block cipher c nonce rk inblock (8*i+2);
       nist_cipher_block cipher c nonce rk inblock (8*i+3);
       nist_cipher_block cipher c nonce rk inblock (8*i+4);
       nist_cipher_block cipher c nonce rk inblock (8*i+5);
       nist_cipher_block cipher c nonce rk inblock (8*i+6);
       nist_cipher_block cipher c nonce rk inblock (8*i+7)]:(int128)list`;
     kterm `ghash_polyval_acc (ghash_twist (cipher (word 0) rk)) tag0
        (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8*i))`;
     kterm `nist_cipher_block cipher c nonce rk inblock (8*i)`]
    GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  (* Both sides are now the same 8-block field element, byteswap-free:       *)
  (* collapse the LHS XOR-of-polyval_dot to a single prop3 (GF(2)-linearity, *)
  (* PROP3_XOR) and match the pmul sums by GF(2) XOR-AC.                     *)
  REWRITE_TAC[ADD_0] THEN
  REWRITE_TAC[polyval_dot] THEN
  REWRITE_TAC[GSYM PROP3_XOR] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;;

(* ========================================================================= *)
(* The main loop: pc+0x4c0 -> pc+0xa10, k iterations.                        *)
(*                                                                           *)
(* The loop body (pc+0x4c0 .. the back-edge b.lt at pc+0xa0c) is             *)
(* software-pipelined: iteration i GHASH-folds the previous group of 8       *)
(* ciphertext blocks (blocks 8i..8i+7, held in v8..v15) while it encrypts    *)
(* and stores the next group (blocks 8(i+1)..8(i+1)+7).  So at the top of    *)
(* iteration i the machine has stored 8*(i+1) ciphertext blocks but GHASHed  *)
(* only 8*i of them; the invariant records this lag.                         *)
(*                                                                           *)
(* Unlike the 4-way kernels, whose loops count down a register and close     *)
(* with cbnz (ENSURES_WHILE_UP_TAC), the back-edge here is a                 *)
(* flag-conditional pointer compare: `cmp x0,x5` (pc+0x9a0) sets the flags   *)
(* and `b.lt` (pc+0xa0c) branches back while x0 < x5 (signed).  So the proof *)
(* uses ENSURES_WHILE_PUP_TAC (the post-test variant) with a flag conjunct   *)
(* `q i s`.  On ARM `b.lt` is taken iff ~(NF <=> VF) (Condition_LT in        *)
(* arm/proofs/instruction.ml), so the flag fact is                           *)
(*      (read NF s <=> read VF s) <=> (i = k)                                *)
(* i.e. GE (fall through) exactly on the last iteration, the ARM analogue of *)
(* the x86 `(read ZF s <=> i = k)` flag fact.                                *)
(*                                                                           *)
(* The precondition is the invariant at i = 0 (at pc+0x4c0), so the init     *)
(* subgoal is a reflexive 0-step ensures; the back-edge and exit subgoals    *)
(* step only the b.lt, which preserves every state conjunct.                 *)
(*                                                                           *)
(* Loop-carried SIMD state pinned by the invariant:                          *)
(* - v8..v15 = the previous group's ciphertext blocks 8i..8i+7, each         *)
(*   `word_xor (aes_ctr_block cipher c nonce rk (8i+j)) (inblock             *)
(*   (8i+j))`, the same form as the stored out-blocks (in iteration i the    *)
(*   stores `stp q8,q9,[x2],#32` .. write q8..q15 to blocks 8(i+1)+0 ..      *)
(*   8(i+1)+7); without them Q19 at the body end would be a GHASH of         *)
(*   unconstrained values;                                                   *)
(* - v0..v4 = rev8 (ctr_block nonce (8i+c+8 .. 8i+c+12)), the counter blocks *)
(*   encrypted in this iteration (the body's first use of each is an         *)
(*   `aese vN,v26`); v5..v7 are recomputed in the body with `rev32 vN,v30`;  *)
(* - Q30 = rev32 (ctr_block nonce (8i+c+13)), the next counter;              *)
(* - Q19 = nist_ghash .. (8*i), the GHASH of the blocks hashed so far.       *)
(*                                                                           *)
(* The antecedent 8 * (k + 1) <= nb keeps the four ciphertext stores (stp    *)
(* q8..q15,[x2],#32 at 0x9e4..0xa04) inside out_p, which the stepper needs   *)
(* in order to show that they do not modify the code.                        *)
(* ========================================================================= *)

let AES_GCM_ENC_ALT_MAIN_LOOP = prove
 (kterm `!in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce c rk inblock nb k pc.
    ~(k = 0) /\
    8 * (k + 1) <= nb /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb)]
      [(in_p, 16 * nb); (key_p, keybytes); (htable_p, 192);
       (tag_p, 16); (ivec_p, 16); (mod_p, 8)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + pc_loop) /\
           read X0 s = word_add in_p (word (128 * (0 + 1))) /\
           read X2 s = word_add out_p (word (128 * (0 + 1))) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           wordlist_from_memory(key_p,nrk) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + c + 13)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8 * 0)) /\
           read Q8 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 0))) (inblock (8 * 0 + 0)) /\
           read Q9 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 1))) (inblock (8 * 0 + 1)) /\
           read Q10 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 2))) (inblock (8 * 0 + 2)) /\
           read Q11 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 3))) (inblock (8 * 0 + 3)) /\
           read Q12 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 4))) (inblock (8 * 0 + 4)) /\
           read Q13 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 5))) (inblock (8 * 0 + 5)) /\
           read Q14 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 6))) (inblock (8 * 0 + 6)) /\
           read Q15 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 7))) (inblock (8 * 0 + 7)) /\
           read Q0 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 8)) /\
           read Q1 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 9)) /\
           read Q2 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 10)) /\
           read Q3 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 11)) /\
           read Q4 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 12)) /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * (0 + 1)
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)) /\
           ((read NF s <=> read VF s) <=> (0 = k)))
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + pc_prepretail) /\
           read X0 s = word_add in_p (word (128 * (k + 1))) /\
           read X2 s = word_add out_p (word (128 * (k + 1))) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           wordlist_from_memory(key_p,nrk) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * k + c + 13)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8 * k)) /\
           read Q8 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * k + 0))) (inblock (8 * k + 0)) /\
           read Q9 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * k + 1))) (inblock (8 * k + 1)) /\
           read Q10 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * k + 2))) (inblock (8 * k + 2)) /\
           read Q11 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * k + 3))) (inblock (8 * k + 3)) /\
           read Q12 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * k + 4))) (inblock (8 * k + 4)) /\
           read Q13 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * k + 5))) (inblock (8 * k + 5)) /\
           read Q14 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * k + 6))) (inblock (8 * k + 6)) /\
           read Q15 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * k + 7))) (inblock (8 * k + 7)) /\
           read Q0 s = word_reversefields 8 (ctr_block nonce (8 * k + c + 8)) /\
           read Q1 s = word_reversefields 8 (ctr_block nonce (8 * k + c + 9)) /\
           read Q2 s = word_reversefields 8 (ctr_block nonce (8 * k + c + 10)) /\
           read Q3 s = word_reversefields 8 (ctr_block nonce (8 * k + c + 11)) /\
           read Q4 s = word_reversefields 8 (ctr_block nonce (8 * k + c + 12)) /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * (k + 1)
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALLPAIRS; ALL] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_WHILE_PUP_TAC `k:num`
    (kterm `pc + pc_loop`) (kterm `pc + pc_backedge`)
    (kterm `\i s. (read X0 s = word_add in_p (word (128 * (i + 1))) /\
            read X2 s = word_add out_p (word (128 * (i + 1))) /\
            read X3 s = tag_p /\
            read X9 s = word (16 * nb) /\
            read X4 s = word_add in_p (word (16 * nb)) /\
            read X16 s = ivec_p /\
            read X5 s = end_p /\
            read X6 s = htable_p /\
            read X10 s = mod_p /\
            read X11 s = key_p /\
            read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
            wordlist_from_memory(key_p,nrk) s =
              MAP (word_reversefields 8) rk /\
            read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
            read (memory :> bytes128 ivec_p) s =
              word_reversefields 8 (ctr_block nonce c) /\
            read Q30 s = word_reversefields 32 (ctr_block nonce (8 * i + c + 13)) /\
            read Q31 s = word 79228162514264337593543950336 /\
            read Q19 s =
              nist_ghash (cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8 * i)) /\
            read Q8 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * i + 0))) (inblock (8 * i + 0)) /\
            read Q9 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * i + 1))) (inblock (8 * i + 1)) /\
            read Q10 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * i + 2))) (inblock (8 * i + 2)) /\
            read Q11 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * i + 3))) (inblock (8 * i + 3)) /\
            read Q12 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * i + 4))) (inblock (8 * i + 4)) /\
            read Q13 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * i + 5))) (inblock (8 * i + 5)) /\
            read Q14 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * i + 6))) (inblock (8 * i + 6)) /\
            read Q15 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * i + 7))) (inblock (8 * i + 7)) /\
            read Q0 s = word_reversefields 8 (ctr_block nonce (8 * i + c + 8)) /\
            read Q1 s = word_reversefields 8 (ctr_block nonce (8 * i + c + 9)) /\
            read Q2 s = word_reversefields 8 (ctr_block nonce (8 * i + c + 10)) /\
            read Q3 s = word_reversefields 8 (ctr_block nonce (8 * i + c + 11)) /\
            read Q4 s = word_reversefields 8 (ctr_block nonce (8 * i + c + 12)) /\
            htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
            (!j. j < nb
                 ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                     inblock j) /\
            (!j. j < 8 * (i + 1)
                 ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                     word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j))) /\
           ((read NF s <=> read VF s) <=> (i = k))`) THEN
  REWRITE_TAC[htable_mem_8; htable_mem_4; KEY_SPLIT] THEN
  REPEAT CONJ_TAC THENL
   [(* Subgoal 1: 0 < k *)
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;

    (* Subgoal 2: init -- reflexive 0-step (precondition = p 0 at pc+0x4c0) *)
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_8; htable_mem_4]) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[];

    (* Subgoal 3: the body, a 339-instruction fused GHASH+AES pipeline.      *)
    (*                                                                       *)
    (* The body is stepped to ENSURES_FINAL_STATE_TAC with all eight         *)
    (* ciphertext register facts (read Q8..Q15 s339) intact.  Steps 1--339   *)
    (* are the body; the b.lt at 0xa0c (step 340) is the back-edge, handled  *)
    (* in subgoals 4 and 5.  The four plaintext reloads `ldp q,q,[x0],#32`   *)
    (* are steps 263/295/303/304: the first resolves directly, the three     *)
    (* post-incremented ones use LDP_STEP4_TAC, which supplies the word_add  *)
    (* flatten and offset normalisation their second-element addresses need  *)
    (* to match the input-block reads (otherwise DISCARD_OLDSTATE            *)
    (* drops them).                                                          *)
    (*                                                                       *)
    (* Counter pins: the setup advances the counter by 13, so at loop entry  *)
    (* v0..v4 = ctr_block nonce (8i+c+8 .. 8i+c+12) and Q30 = ctr(8i+c+13);  *)
    (* the invariant pins Q0..Q4/Q30 to those block-index values, and the    *)
    (* out-forall is stated in block-index aes_ctr_block form.               *)
    (*                                                                       *)
    (* The stores `stp q,q,[x2],#32` at steps 330/334/337/338 (pc            *)
    (* 0x9e4/0x9f4/0xa00/0xa04) write the new blocks 8i+8..8i+15.  The       *)
    (* incoming out-forall is carried across them by the ordinary stepper    *)
    (* and survives to s339; the 8 new blocks close from the concrete store  *)
    (* facts.  The Q19 GHASH fold is Q19_FOLD_TAC (above).  The other        *)
    (* conjuncts (X registers, key/htable/tag/ivec memory, Q30/Q31, the      *)
    (* Q0..Q4 counters, the Q8..Q15 ciphertext, the new out-blocks, flag,    *)
    (* PC) close in the cheap close: the case split on the bound             *)
    (* 8*((i+1)+1), eor3 AC-normalisation by WORD_BITWISE_RULE,              *)
    (* CTR_BLOCK_RECONSTRUCT_REV8/REV32 + WORD_SUBWORD_* +                   *)
    (* XOR_CIPHER_RECONSTRUCT + aes_ctr_block/ADD_CLAUSES, then              *)
    (* WORD_RULE, AP_THM/AP_TERM peeling and ARITH.                          *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `read (memory :> bytes128 (word_add in_p (word (128 * (i + 1))))) s0 =
      inblock (8 * (i + 1)) /\
      read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 16)))) s0 =
      inblock (8 * (i + 1) + 1) /\
      read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 32)))) s0 =
      inblock (8 * (i + 1) + 2) /\
      read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 48)))) s0 =
      inblock (8 * (i + 1) + 3) /\
      read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 64)))) s0 =
      inblock (8 * (i + 1) + 4) /\
      read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 80)))) s0 =
      inblock (8 * (i + 1) + 5) /\
      read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 96)))) s0 =
      inblock (8 * (i + 1) + 6) /\
      read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 112)))) s0 =
      inblock (8 * (i + 1) + 7)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE
       `128 * (i + 1) + 16 = 16 * (8 * (i + 1) + 1) /\
        128 * (i + 1) + 32 = 16 * (8 * (i + 1) + 2) /\
        128 * (i + 1) + 48 = 16 * (8 * (i + 1) + 3) /\
        128 * (i + 1) + 64 = 16 * (8 * (i + 1) + 4) /\
        128 * (i + 1) + 80 = 16 * (8 * (i + 1) + 5) /\
        128 * (i + 1) + 96 = 16 * (8 * (i + 1) + 6) /\
        128 * (i + 1) + 112 = 16 * (8 * (i + 1) + 7)`] THEN
      REWRITE_TAC[ARITH_RULE `128 * a = 16 * 8 * a`] THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES_GCM_ENC_ALT_EXEC]
      (kterm `LENGTH tmc`)]) THEN
    MAP_EVERY NSTEP_G (1--(loop_ldp1-1)) THEN
    LDP_STEP4_TAC loop_ldp1 THEN
    MAP_EVERY NSTEP_G ((loop_ldp1+1)--(loop_ldp2-1)) THEN
    LDP_STEP4_TAC loop_ldp2 THEN
    LDP_STEP4_TAC (loop_ldp2+1) THEN
    MAP_EVERY NSTEP_G ((loop_ldp2+2)--(loop_backedge-1)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    (* Cheap-conjunct close.  The case-split bound is 8*((i+1)+1) (the       *)
    (* invariant's out-forall at i is j < 8*(i+1), so at i+1 it is           *)
    (* j < 8*(i+2)); the eor3 3-way store XOR is AC-normalised to the        *)
    (* XOR_CIPHER_RECONSTRUCT shape; then CIPHER_KEYLIST                     *)
    (* collapses the residual explicit key list `[EL 0 rk;..;EL nr rk]` back *)
    (* to `rk` (XOR_CIPHER_RECONSTRUCT + MAP leaves the list,                *)
    (* not `rk`).                                                            *)
    (*                                                                       *)
    (* The raw post-FINAL_STATE conjunction is split first, before the cheap *)
    (* close, so that the Q19 conjunct is folded while its ext/LO structure  *)
    (* is intact: the cheap close's WORD_SIMPLE_SUBWORD_CONV would destroy   *)
    (* it.  The per-goal dispatcher routes each conjunct:                    *)
    (* - Q19 (RHS headed by nist_ghash): Q19_FOLD_TAC;                       *)
    (* - the counter registers Q0..Q4 / Q30 (RHS headed by                   *)
    (*   word_reversefields): lane reconstruction + ARITH;                   *)
    (* - everything else: the cheap-close rewrites, which also do the        *)
    (*   out-forall case split.                                              *)
    REPEAT CONJ_TAC THEN
    (fun (asl,w as gl) ->
      if is_eq w &&
         (try fst(dest_const(fst(strip_comb(rhs w)))) = "nist_ghash"
          with _ -> false)
      then Q19_FOLD_TAC gl
      else if is_eq w &&
         (try fst(dest_const(fst(strip_comb(rhs w)))) = "word_reversefields"
          with _ -> false)
      then
       (* counter-register conjuncts (Q0..Q4 rev8 / Q30 rev32): reconstruct
          the lane word_joins to ctr_block form, then discharge the
          counter-index equality (equal by arithmetic, not syntactically
          identical) by ARITH. *)
       (REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
        REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
        REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8; CTR_BLOCK_RECONSTRUCT_REV32] THEN
        AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC) gl
      else
       (REWRITE_TAC[MAIN_LOOP_OUT_DISJSPLIT] THEN
        ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
        REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
        REWRITE_TAC[ARITH_RULE `16 * (8 * (i+1) + b) = 128 * (i+1) + 16 * b`] THEN
        REWRITE_TAC[ARITH_RULE `16 * 8 * (i+1) = 128 * (i+1)`] THEN
        CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
        REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
        REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8; CTR_BLOCK_RECONSTRUCT_REV32] THEN
        ONCE_REWRITE_TAC[WORD_BITWISE_RULE
          `word_xor (word_xor (inb:int128) ch) rkn =
           word_xor ch (word_xor rkn inb)`] THEN
        REWRITE_TAC[XOR_CIPHER_RECONSTRUCT] THEN
        ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
        REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
        CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
        ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; ARITH_RULE `i < l ==> i + 1 <= l`] THEN
        REWRITE_TAC[ADD_ASSOC; ARITH] THEN
        (* collapse the explicit key list to rk before folding, then refold
           both sides to aes_ctr_block form.  A plain GSYM cipher_block fold
           is ambiguous under the c parameter (the inblock/i higher-order
           match spuriously picks c := 8*i+c), so instead close the
           ciphertext identity directly at the aes_ctr_block level: peel the
           word_xor and aes_ctr_block by AP_THM/AP_TERM and discharge the
           counter-index equality by ARITH.  Pointer conjuncts fall
           to WORD_RULE. *)
        REWRITE_TAC[CIPHER_KEYLIST] THEN
        REWRITE_TAC[aes_ctr_block; ADD_CLAUSES] THEN
        REPEAT CONJ_TAC THEN
        TRY(CONV_TAC WORD_RULE) THEN
        REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
        TRY ARITH_TAC) gl) THEN
    (* What remains after the dispatcher is the flag conjunct q(i+1) =       *)
    (* ((NF<=>VF) <=> (i+1 = k)) and the MAYCHANGE frame-subsumption goal,   *)
    (* split by REPEAT CONJ_TAC.  MAIN_LOOP's two end_p antecedents (end_p = *)
    (* word_add in_p (word (128*(k+1))) and the no-wrap bound val in_p +     *)
    (* 128*(k+1) < 2 EXP 63) pin the iteration count k.  The cheap close's   *)
    (* WORD_ADD normalisation splits the flag offsets to word_add (word      *)
    (* (128*i)) (word 256) (= X0 = in_p + 128*(i+2)) and word_add (word      *)
    (* (128*k)) (word 128) (= end_p, already substituted by ASM_REWRITE), so *)
    (* the flag close is not syntactic: it rewrites with BRIDGE_GE (the      *)
    (* NF<>VF biconditional = signed GE ival end_p <= ival X0), linearises   *)
    (* both additive ivals with IVAL_PTR_ADD under the no-wrap bound, and    *)
    (* finishes by arithmetic using i < k.                                   *)
    REPEAT CONJ_TAC THEN
    (* Fire the flag close only on the flag-shaped goal, the one whose
       conclusion is `<flag biconditional> <=> (i + 1 = k)`; this keeps
       BRIDGE_GE off the large Q19 term.  flag_arith undischarges only the
       two needed hypotheses (`i < k` and the no-wrap bound) before a bare
       ARITH_TAC; ASM_ARITH_TAC would have to consider every hypothesis,
       including the large ciphertext and Q19 terms. *)
    (let flag_arith =
       UNDISCH_TAC `val(in_p:int64) + 128 * (k + 1) < 2 EXP 63` THEN
       UNDISCH_TAC `(i:num) < k` THEN ARITH_TAC in
     fun (asl,w as gl) ->
       (if (can (term_match [] `xxx:bool <=> (i:num) + 1 = k`) w)
        then
         (REWRITE_TAC[BRIDGE_GE] THEN
          MP_TAC(SPECL [`in_p:int64`; `128 * i + 256`] IVAL_PTR_ADD) THEN
          ANTS_TAC THENL [flag_arith; ALL_TAC] THEN
          MP_TAC(SPECL [`in_p:int64`; `128 * k + 128`] IVAL_PTR_ADD) THEN
          ANTS_TAC THENL [flag_arith; ALL_TAC] THEN
          REWRITE_TAC[GSYM WORD_ADD] THEN
          DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
          REWRITE_TAC[INT_OF_NUM_LE] THEN flag_arith)
        (* the only residual reaching this branch is the MAYCHANGE
           frame-subsumption goal `(<accumulated>) s0 s339`.  The body
           overwrites all of Q8..Q15 (the in-flight ciphertext blocks),
           whose low 64 bits the ABI frame does not allow to change (d8-d15
           are callee-saved); so the MAIN_LOOP frame includes `MAYCHANGE
           [Q8;..;Q15]`, as in the 4-way kernels, and the subroutine's
           d8-d15 epilogue restores the low halves.  MONOTONE_MAYCHANGE_TAC
           discharges the subsumption (the 8 ciphertext stores
           bytes128(out_p+128*(i+1)+16m) lie in bytes(out_p,16*nb) by the
           `8*(k+1)<=nb` antecedent). *)
        else MONOTONE_MAYCHANGE_TAC) gl);

    (* Subgoal 4: back-edge taken (0 < i < k => b.lt branches back) *)
    REPEAT STRIP_TAC THEN
    ARM_SIM_TAC AES_GCM_ENC_ALT_EXEC [1] THEN
    ASM_REWRITE_TAC[];

    (* Subgoal 5: exit fall-through (i = k => GE, b.lt not taken) *)
    REPEAT STRIP_TAC THEN
    ARM_SIM_TAC AES_GCM_ENC_ALT_EXEC [1] THEN
    ASM_REWRITE_TAC[]]);;

(* CIPHER_CLOSE: the MAIN_LOOP body ciphertext chain (in                     *)
(* AES_GCM_ENC_ALT_MAIN_LOOP) specialised to SETUP.  Reduces the raw         *)
(* eor3/aese form                                                            *)
(*      word_xor (word_xor (inblock j) (aese..aese..rk(nr-1))) rkn           *)
(* to the cipher form.  For block 0 (counter ctr_block nonce c, no           *)
(* rev32 rebuild) it closes outright; for the out-forall's j = 1..7 it       *)
(* leaves the AES-input identity residual that CIPHER_ID_TAC then peels.     *)
let CIPHER_CLOSE =
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rkn =
     word_xor ch (word_xor rkn inb)`] THEN
  REWRITE_TAC[XOR_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  (* The AES input is the raw rev8 counter-lane assembly for block K.
     Reconstruct it to ctr_block nonce (c+K) (CTR_LANE_LOW + CTR_NONCE_LANES
     + GSYM WORD_ADD + CTR_BLOCK_RECONSTRUCT_REV8/REV32, then cancel the
     outer double reverse), collapse the keys, refold to aes_ctr_block, then
     peel word_xor + aes_ctr_block and discharge the counter-index equality
     by ARITH.  (A plain GSYM cipher_block fold is higher-order ambiguous
     under c.) *)
  REWRITE_TAC[CTR_LANE_LOW; CTR_NONCE_LANES] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8; CTR_BLOCK_RECONSTRUCT_REV32] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[CIPHER_KEYLIST] THEN
  REWRITE_TAC[aes_ctr_block; ADD_CLAUSES] THEN
  (* normalise the 8*0+j indices so that the block-0 special case (bare
     counter c and inblock 0 on the LHS vs c+8*0+0 / inblock (8*0+0) on the
     RHS) matches. *)
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
  TRY(REFL_TAC) THEN
  TRY(REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN ARITH_TAC);;

(* SETUP_RECON_TAC_GEN routes each SETUP residual by its shape: the negated  *)
(* flag conjunct -> FLAG_CLOSE_GEN; the out-forall -> 8-way case split +     *)
(* CIPHER_CLOSE / CIPHER_ID_TAC; a nist_ghash RHS (Q19 = tag0) ->            *)
(* NIST_GHASH_NIL; word_xor = word_xor (the ciphertext registers) ->         *)
(* CIPHER_CLOSE; word_join = word_reversefields (the counters) -> CTR_CLOSE; *)
(* word_add (the pointer registers) -> WORD_RULE, the X4 word_ushr bridge or *)
(* SETUP_X5_END_GEN; any other read (the surviving read-only facts)          *)
(* -> ASM_REWRITE.                                                           *)
let SETUP_RECON_TAC_GEN : tactic =
  fun (asl,w as gl) ->
    if is_neg w then FLAG_CLOSE_GEN gl
    else if is_forall w then
      (REWRITE_TAC[ARITH_RULE `j < 8 * (0 + 1) <=>
                     j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/
                     j = 4 \/ j = 5 \/ j = 6 \/ j = 7`] THEN
       REWRITE_TAC[TAUT `(p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)`] THEN
       REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
       CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
       REWRITE_TAC[WORD_ADD_0] THEN
       REPEAT CONJ_TAC THEN CIPHER_CLOSE THEN TRY CIPHER_ID_TAC THEN
       TRY CIPHER_CLOSE) gl
    else if is_eq w then
      let l,r = dest_eq w in
      let rhd = try fst(dest_const(fst(strip_comb r))) with _ -> "?" in
      let lhd = try fst(dest_const(fst(strip_comb l))) with _ -> "?" in
      if rhd = "nist_ghash" then
        (CONV_TAC NUM_REDUCE_CONV THEN
         REWRITE_TAC[list_of_seq; NIST_GHASH_NIL] THEN CONV_TAC WORD_BLAST) gl
      else if lhd = "word_xor" && rhd = "word_xor" then
        (CIPHER_CLOSE THEN TRY CIPHER_ID_TAC THEN TRY CIPHER_CLOSE) gl
      else if lhd = "word_join" && rhd = "word_reversefields" then
        CTR_CLOSE gl
      else if lhd = "word_add" then
        FIRST
          [CONV_TAC WORD_RULE;
           (AP_TERM_TAC THEN REWRITE_TAC[word_ushr; VAL_WORD; DIMINDEX_64] THEN
            AP_TERM_TAC THEN ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC);
           (ASM_SIMP_TAC[SETUP_X5_END_GEN])] gl
      else (* surviving read-only reads (keys/htable/ivec/tag/stack) *)
        (ASM_REWRITE_TAC[ARITH_RULE `(128 * nb) DIV 8 = 16 * nb`] THEN
         CONV_TAC NUM_REDUCE_CONV) gl
    else ASM_REWRITE_TAC[] gl;;

(* ========================================================================= *)
(* SETUP (pipeline fill): pc+0x38 -> pc+0x4c0.                               *)
(*                                                                           *)
(* Core entry pc+0x38 is just after the prologue (stack adjust, d8-d15       *)
(* spills, modulus-constant store and the X9/X16/X11/X10 set-up).  This      *)
(* region: 0x38-0xb4 builds the 8 CTR keystream inputs v0..v7 (rev32 of the  *)
(* counter), tests nb <= 4 (cmp x9,#0x40 / b.le L256_enc_small at 0x4c/0x50, *)
(* steps 6-7, not taken for nb >= 5), computes the loop-end pointer X5       *)
(* (0x6c-0x74) and loads rk0/rk1; the tag is loaded into Q19 at 0xb8 (ld1    *)
(* v19; ext; rev64, giving tag0 itself); 0xc8-0x440 runs the nr AES rounds   *)
(* on v0..v7; 0x444 sets X4 = in_p + byte_len (the input end pointer) and    *)
(* 0x44c does the b.ge tail check (not taken for nb >= 9); 0x450-0x4b8 loads *)
(* the 8 plaintext blocks (four ldp q,q,[x0],#32), eor3s them with the       *)
(* keystream and rkn into ciphertext, rev32s the next counters into v0..v4   *)
(* and stores the 8 ciphertext blocks (four stp q,q,[x2],#32); 0x4bc does    *)
(* the b.ge prepretail check (not taken for nb >= 17) and falls through to   *)
(* the main-loop top 0x4c0.                                                  *)
(*                                                                           *)
(* SETUP_GEN establishes MAIN_LOOP's precondition at i = 0 for k >= 1, with  *)
(* 8*(k+1) < nb <= 8*(k+2), i.e. k = (nb-1) DIV 8 - 1.  The loop body uses   *)
(* only X0, X2, X5, X6, X10 and X11, so X4 = in_p+16*nb (the input end       *)
(* pointer, used by the tail) and X16 = ivec_p (for the final                *)
(* `str q30,[x16]` ivec writeback) are set up here and carried through the   *)
(* loop unchanged.                                                           *)
(*                                                                           *)
(* mod_p is the on-stack modulus constant at stackpointer+0x40               *)
(* (add x10,sp,#0x40 at 0x34; the 0xc2..0 constant is stored there at 0x30). *)
(* The core is stated with mod_p = word_add stackpointer (word 0x40); the    *)
(* subroutine wrapper ties stackpointer to the caller's SP - 0x50.           *)
(*                                                                           *)
(* The drive is 290 steps: NSTEP 1-7 (the b.le at step 7 resolved by         *)
(* DISPATCH4_NOT_TAKEN and DISPATCH_SMALL_NOT_TAKEN), 8-261, NSTEP 262 = the *)
(* b.ge at 0x44c (SETUP_BRANCH_COND_FALSE_GEN), LDP_SETUP_TAC at the four    *)
(* ldps (steps 263/264/272/273; the stps are steps 278/279/286/288), and     *)
(* NSTEP 290 = the b.ge at 0x4bc (SETUP_BRANCH_COND_FALSE_2_GEN).  The final *)
(* state is then closed by SETUP_RECON_TAC_GEN, like the MAIN_LOOP body's    *)
(* cheap close: XOR_CIPHER_RECONSTRUCT + aes_ctr_block/ADD_CLAUSES +         *)
(* CIPHER_KEYLIST for Q8..Q15, CTR_BLOCK_RECONSTRUCT_* for Q0..Q4 and        *)
(* Q30, and Q19 = nist_ghash..(8*0) = tag0.                                  *)
(* ========================================================================= *)

let AES_GCM_ENC_ALT_SETUP_GEN = prove
 (kterm `!in_p out_p tag_p ivec_p key_p htable_p stackpointer len_bits end_p
     tag0 nonce c rk inblock nb k pc.
    ~(k = 0) /\
    8 * (k + 1) <= nb /\
    len_bits = 128 * nb /\
    8 * (k + 1) < nb /\ nb <= 8 * (k + 2) /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb)]
      [(in_p, 16 * nb); (key_p, keybytes); (htable_p, 192);
       (tag_p, 16); (ivec_p, 16); (word_add stackpointer (word 0x40), 8)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word len_bits /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (len_bits DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           wordlist_from_memory(key_p,nrk) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + pc_loop) /\
           read X0 s = word_add in_p (word (128 * (0 + 1))) /\
           read X2 s = word_add out_p (word (128 * (0 + 1))) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X11 s = key_p /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           wordlist_from_memory(key_p,nrk) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + c + 13)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8 * 0)) /\
           read Q8 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 0))) (inblock (8 * 0 + 0)) /\
           read Q9 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 1))) (inblock (8 * 0 + 1)) /\
           read Q10 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 2))) (inblock (8 * 0 + 2)) /\
           read Q11 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 3))) (inblock (8 * 0 + 3)) /\
           read Q12 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 4))) (inblock (8 * 0 + 4)) /\
           read Q13 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 5))) (inblock (8 * 0 + 5)) /\
           read Q14 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 6))) (inblock (8 * 0 + 6)) /\
           read Q15 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 7))) (inblock (8 * 0 + 7)) /\
           read Q0 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 8)) /\
           read Q1 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 9)) /\
           read Q2 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 10)) /\
           read Q3 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 11)) /\
           read Q4 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 12)) /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * (0 + 1)
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)) /\
           ((read NF s <=> read VF s) <=> (0 = k)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb)])`,
  REWRITE_TAC[KEY_SPLIT] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALLPAIRS; ALL;
              NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES_GCM_ENC_ALT_EXEC]
      (kterm `LENGTH tmc`)]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_8; htable_mem_4]) THEN
  SUBGOAL_THEN `~(nb = 4)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `5 <= nb` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY NSTEP (1--5) THEN NSTEP 6 THEN NSTEP 7 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[
    MATCH_MP DISPATCH4_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 4)`));
    MATCH_MP DISPATCH_SMALL_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `5 <= nb`));
    COND_CLAUSES]) THEN
  MAP_EVERY NSTEP (8--36) THEN
  MAP_EVERY NSTEP (37--(setup_tail_branch-1)) THEN NSTEP setup_tail_branch THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SETUP_BRANCH_COND_FALSE_GEN
    (CONJ (ASSUME `8 * (k + 1) < nb`) (CONJ (ASSUME `nb <= 8 * (k + 2)`)
          (ASSUME `val (in_p:int64) + 128 * (k + 1) < 2 EXP 63`))); COND_CLAUSES]) THEN
  SETUP_LOADS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SETUP_BRANCH_COND_FALSE_2_GEN
    (CONJ (ASSUME `~(k = 0)`) (CONJ (ASSUME `8 * (k + 1) < nb`)
      (CONJ (ASSUME `nb <= 8 * (k + 2)`)
          (ASSUME `val (in_p:int64) + 128 * (k + 1) < 2 EXP 63`))));
    COND_CLAUSES]) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[htable_mem_8; htable_mem_4] THEN
  REPEAT CONJ_TAC THEN SETUP_RECON_TAC_GEN);;

(* ------------------------------------------------------------------------- *)
(* SETUP_G1: the g = 1 (k = 0) pipeline-fill setup leg, nblocks 9..16.  Its  *)
(* drive is SETUP_GEN's except that at step 290 the second guard (b.ge at    *)
(* 0x4bc) is taken, because end_p = in_p+128*(0+1) = in_p+128 = X0, so the   *)
(* PC goes to pc+0xa10 (PREPRETAIL) instead of the main-loop top pc+0x4c0;   *)
(* SETUP_BRANCH_COND_TRUE_2 discharges it.  The postcondition is             *)
(* PREPRETAIL_GEN's precondition at pc+0xa10 in the k = 0 (8*0) form,        *)
(* without the flag conjunct.                                                *)
(* ------------------------------------------------------------------------- *)
let AES_GCM_ENC_ALT_SETUP_G1 = prove
 (kterm `!in_p out_p tag_p ivec_p key_p htable_p stackpointer len_bits end_p
     tag0 nonce c rk inblock nb k pc.
    k = 0 /\
    8 * (k + 1) <= nb /\
    len_bits = 128 * nb /\
    8 * (k + 1) < nb /\ nb <= 8 * (k + 2) /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb)]
      [(in_p, 16 * nb); (key_p, keybytes); (htable_p, 192);
       (tag_p, 16); (ivec_p, 16); (word_add stackpointer (word 0x40), 8)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word len_bits /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (len_bits DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           wordlist_from_memory(key_p,nrk) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + pc_prepretail) /\
           read X0 s = word_add in_p (word (128 * (0 + 1))) /\
           read X2 s = word_add out_p (word (128 * (0 + 1))) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X11 s = key_p /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           wordlist_from_memory(key_p,nrk) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + c + 13)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8 * 0)) /\
           read Q8 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 0))) (inblock (8 * 0 + 0)) /\
           read Q9 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 1))) (inblock (8 * 0 + 1)) /\
           read Q10 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 2))) (inblock (8 * 0 + 2)) /\
           read Q11 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 3))) (inblock (8 * 0 + 3)) /\
           read Q12 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 4))) (inblock (8 * 0 + 4)) /\
           read Q13 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 5))) (inblock (8 * 0 + 5)) /\
           read Q14 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 6))) (inblock (8 * 0 + 6)) /\
           read Q15 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 7))) (inblock (8 * 0 + 7)) /\
           read Q0 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 8)) /\
           read Q1 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 9)) /\
           read Q2 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 10)) /\
           read Q3 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 11)) /\
           read Q4 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 12)) /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * (0 + 1)
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb)])`,
  REWRITE_TAC[KEY_SPLIT] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALLPAIRS; ALL;
              NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES_GCM_ENC_ALT_EXEC]
      (kterm `LENGTH tmc`)]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_8; htable_mem_4]) THEN
  SUBGOAL_THEN `~(nb = 4)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `5 <= nb` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY NSTEP (1--5) THEN NSTEP 6 THEN NSTEP 7 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[
    MATCH_MP DISPATCH4_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 4)`));
    MATCH_MP DISPATCH_SMALL_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `5 <= nb`));
    COND_CLAUSES]) THEN
  MAP_EVERY NSTEP (8--36) THEN
  MAP_EVERY NSTEP (37--(setup_tail_branch-1)) THEN NSTEP setup_tail_branch THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SETUP_BRANCH_COND_FALSE_GEN
    (CONJ (ASSUME `8 * (k + 1) < nb`) (CONJ (ASSUME `nb <= 8 * (k + 2)`)
          (ASSUME `val (in_p:int64) + 128 * (k + 1) < 2 EXP 63`))); COND_CLAUSES]) THEN
  SETUP_LOADS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SETUP_BRANCH_COND_TRUE_2
    (CONJ (ASSUME `k = 0`) (CONJ (ASSUME `8 * (k + 1) < nb`)
      (CONJ (ASSUME `nb <= 8 * (k + 2)`)
          (ASSUME `val (in_p:int64) + 128 * (k + 1) < 2 EXP 63`))));
    COND_CLAUSES]) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[htable_mem_8; htable_mem_4] THEN
  REPEAT CONJ_TAC THEN SETUP_RECON_TAC_GEN);;

(* ========================================================================= *)
(* PREPRETAIL (pipeline drain): pc+0xa10 -> pc+0xee0 (L256_enc_tail).        *)
(*                                                                           *)
(* The software pipeline runs one 8-block GHASH group behind the ciphertext  *)
(* stores.  At MAIN_LOOP exit (i = k) the last in-flight group (ciphertext   *)
(* blocks 8k..8k+7, held in v8..v15) has been stored but not yet GHASHed;    *)
(* Q19 still holds nist_ghash..(8*k).  PREPRETAIL folds that group into Q19, *)
(* advancing it to nist_ghash..(8*(k+1)), and runs the AES rounds of the     *)
(* next 8 counter blocks (v0..v7, up to the final rkn XOR) that the tail     *)
(* consumes.  It performs no ciphertext stores and no plaintext loads (all   *)
(* `[x0]`/`[x2]` accesses are in the tail, at or after 0xee0) and leaves     *)
(* every general-purpose register (X0, X2, X3, X4, X5, X6, X10, X11, X16)    *)
(* unchanged: no instruction in 0xa10..0xedc writes them.                    *)
(*                                                                           *)
(* The PREPRETAIL precondition is the MAIN_LOOP postcondition at i = k (the  *)
(* state at pc+0xa10), plus aligned_bytes_loaded; ENSURES_SEQUENCE_TAC joins *)
(* them in the composition.  The Q19 drain fold has the same structure as    *)
(* the MAIN_LOOP body's (a leading `ext v19`, at 0xa78 here, the same        *)
(* pmull/pmull2/eor3 Karatsuba chain, the final reduce                       *)
(* `eor3 v19,v19,v21,v17` at 0xec0, and no trailing `ext v19`), so it closes *)
(* by Q19_FOLD_TAC_K, which is Q19_FOLD_TAC with i -> k.  The drain's reduce *)
(* reads v18 through pmull (0xe64, into Q17) and through ext (0xe9c, into    *)
(* Q21); NSTEP_GP (below) also protects Q20/Q21 from the per-step subword    *)
(* normalisation, so both copies of v18 keep the same form and RECON_GRR can *)
(* fold the reduce.  With NSTEP_GP the accumulators Q17/Q18/Q19 stay         *)
(* concrete through the 308-step drive; after FINAL_STATE + REPEAT CONJ_TAC  *)
(* ten residuals remain: the Q30 counter, the Q19 fold and the eight v0..v7  *)
(* AES reconstructions (PP_DISPATCH; the rest close by ASM_REWRITE).         *)
(*                                                                           *)
(* Exit state (after the 308-step drive):                                    *)
(* - PC = pc+0xee0; X0..X16 and Q31 preserved;                               *)
(* - Q28 = word_reversefields 8 (EL nr rk) (rkn, the tail's final            *)
(*   round key);                                                             *)
(* - Q30 = word_reversefields 32 (ctr_block nonce (8*k+c+16)): the three     *)
(*   `add v30` at 0xa18/0xa24/0xea8 each add 1 to the counter lane;          *)
(* - Q0..Q4 = the aese/aesmc chain with rk0..rk(nr-1) (the state before the  *)
(*   final rkn XOR) over word_reversefields 8 (ctr_block nonce (8*k+c+8+j))  *)
(*   (the counter blocks pinned by the loop invariant);                      *)
(* - Q5..Q7 = the same chain over the counters 8*k+c+13 .. 8*k+c+15, built   *)
(*   with rev32 from the incremented v30.                                    *)
(* The postcondition states v0..v7 in forms XOR_CIPHER_RECONSTRUCT           *)
(* reduces (word_xor (read Qj) rkn = word_reversefields 8 (cipher            *)
(* ...)), matching the setup's convention and what the tail consumes (the    *)
(* tail's first `eor3 v9,v8,v0,v29` XORs v0 with v29, a copy of v28 = rkn).  *)
(* ========================================================================= *)

(* NSTEP_GP: the stepper for the prepretail, the tail arms and the small     *)
(* path tails.  It skips all three per-step normalisations on assumptions    *)
(* that mention the accumulators Q17..Q21 (is_ghash_acc_pp): the word_add    *)
(* flatten and NORMOFF are the identity on them and the subword pass must    *)
(* not touch them.  On the other facts the word_add flatten and NORMOFF run  *)
(* only when has_wadd_nest / has_word_of_sum find their redex, since they    *)
(* are no-ops otherwise.                                                     *)
let NSTEP_GP n =
  ARM_STEPS_TAC AES_GCM_ENC_ALT_EXEC [n] THEN
  RULE_ASSUM_TAC(fun th ->
    if is_ghash_acc_pp th then th
    else
      let th1 = if has_wadd_nest (concl th) then NSTEP_GP_WADD_RULE th else th in
      let th2 = if has_word_of_sum (concl th1) then NORMOFF_RULE th1 else th1 in
      SUBWORD_NORM_RULE th2);;

(* The Q19 drain fold: Q19_FOLD_TAC with the accumulator index i -> k (the   *)
(* drain folds the last in-flight 8-block group at loop bound k, advancing   *)
(* Q19 from nist_ghash..(8*k) to nist_ghash..(8*(k+1))).  The fold has the   *)
(* same structure as the main-loop body's; see Q19_FOLD_TAC for the route.   *)
let Q19_FOLD_TAC_K =
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (x:int128) e) p = word_xor (word_xor x p) e`] THEN
  REWRITE_TAC[RECON_GRR] THEN
  REWRITE_TAC[GSYM cipher_block] THEN REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_DIST8_PLAIN] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE
    `8 * (k + 1) = SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(8 * k))))))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  MP_TAC(ISPECL
    [kterm `ghash_twist (cipher (word 0) rk)`;
     kterm `[nist_cipher_block cipher c nonce rk inblock (8*k+1);
       nist_cipher_block cipher c nonce rk inblock (8*k+2);
       nist_cipher_block cipher c nonce rk inblock (8*k+3);
       nist_cipher_block cipher c nonce rk inblock (8*k+4);
       nist_cipher_block cipher c nonce rk inblock (8*k+5);
       nist_cipher_block cipher c nonce rk inblock (8*k+6);
       nist_cipher_block cipher c nonce rk inblock (8*k+7)]:(int128)list`;
     kterm `ghash_polyval_acc (ghash_twist (cipher (word 0) rk)) tag0
        (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8*k))`;
     kterm `nist_cipher_block cipher c nonce rk inblock (8*k)`]
    GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ADD_0] THEN
  REWRITE_TAC[polyval_dot] THEN
  REWRITE_TAC[GSYM PROP3_XOR] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;;

(* v0..v7 AES closer.  v0..v4 are pinned as word_reversefields 8 (ctr_block  *)
(* ..), so CIPHER_RECONSTRUCT + MAP + CIPHER_KEYLIST close                   *)
(* them directly.  v5..v7 are freshly rev32'd from the incremented v30, so   *)
(* the AES reconstruction leaves a plaintext residual word_reversefields 8   *)
(* (cipher <rev-lanes> rk) = ..(ctr_block ..), which the counter-lane        *)
(* reconstruction (WORD_SUBWORD_*32 + CTR_BLOCK_RECONSTRUCT_REV8 +           *)
(* WORD_REVERSEFIELDS_REVERSEFIELDS) folds; the TRY makes it a no-op for     *)
(* v0..v4 (already closed).                                                  *)
let PP_AES_CLOSE =
  ASM_REWRITE_TAC[CIPHER_RECONSTRUCT; MAP;
                  WORD_REVERSEFIELDS_REVERSEFIELDS; CIPHER_KEYLIST] THEN
  TRY(REWRITE_TAC[GSYM WORD_ADD] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
      REWRITE_TAC[GSYM WORD_ADD] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
      REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      REFL_TAC);;

(* Shape-routed per-goal dispatcher over the 10 post-FINAL_STATE residuals:  *)
(* nist_ghash-RHS -> Q19 fold; word_join=word_reversefields -> Q30 counter;  *)
(* the 8 v-register AES eqs -> PP_AES_CLOSE; anything else -> ASM_REWRITE.   *)
let PP_DISPATCH : tactic = fun (asl,w as gl) ->
  if is_eq w then
    let l,r = dest_eq w in
    let rhd = try fst(dest_const(fst(strip_comb r))) with _ -> "?" in
    let lhd = try fst(dest_const(fst(strip_comb l))) with _ -> "?" in
    if rhd = "nist_ghash" then Q19_FOLD_TAC_K gl
    else if lhd = "word_join" && rhd = "word_reversefields" then PP_CTR_CLOSE gl
    else PP_AES_CLOSE gl
  else ASM_REWRITE_TAC[] gl;;

(* ------------------------------------------------------------------------- *)
(* PREPRETAIL_GEN: the pipeline-drain theorem, for every k including k = 0   *)
(* (the g = 1 leg, nblocks 9..16, where the main loop runs zero times and    *)
(* the prepretail and the tail do all the work).  The proof is a             *)
(* straight-line drive, MAP_EVERY NSTEP_GP (1--prepretail_steps), then       *)
(* FINAL_STATE and PP_DISPATCH; nothing in it depends on k beyond the        *)
(* symbolic 8*k.                                                             *)
(* ------------------------------------------------------------------------- *)
let AES_GCM_ENC_ALT_PREPRETAIL_GEN = prove
 (kterm `!in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce c rk inblock nb k pc.
    8 * (k + 1) <= nb /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb)]
      [(in_p, 16 * nb); (key_p, keybytes); (htable_p, 192);
       (tag_p, 16); (ivec_p, 16); (mod_p, 8)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + pc_prepretail) /\
           read X0 s = word_add in_p (word (128 * (k + 1))) /\
           read X2 s = word_add out_p (word (128 * (k + 1))) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           wordlist_from_memory(key_p,nrk) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * k + c + 13)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8 * k)) /\
           read Q8 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * k + 0))) (inblock (8 * k + 0)) /\
           read Q9 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * k + 1))) (inblock (8 * k + 1)) /\
           read Q10 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * k + 2))) (inblock (8 * k + 2)) /\
           read Q11 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * k + 3))) (inblock (8 * k + 3)) /\
           read Q12 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * k + 4))) (inblock (8 * k + 4)) /\
           read Q13 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * k + 5))) (inblock (8 * k + 5)) /\
           read Q14 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * k + 6))) (inblock (8 * k + 6)) /\
           read Q15 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * k + 7))) (inblock (8 * k + 7)) /\
           read Q0 s = word_reversefields 8 (ctr_block nonce (8 * k + c + 8)) /\
           read Q1 s = word_reversefields 8 (ctr_block nonce (8 * k + c + 9)) /\
           read Q2 s = word_reversefields 8 (ctr_block nonce (8 * k + c + 10)) /\
           read Q3 s = word_reversefields 8 (ctr_block nonce (8 * k + c + 11)) /\
           read Q4 s = word_reversefields 8 (ctr_block nonce (8 * k + c + 12)) /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * (k + 1)
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + pc_tail) /\
           read X0 s = word_add in_p (word (128 * (k + 1))) /\
           read X2 s = word_add out_p (word (128 * (k + 1))) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           wordlist_from_memory(key_p,nrk) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q28 s = word_reversefields 8 (EL nr rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * k + c + 16)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8 * (k + 1))) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * k + c + 8)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * k + c + 9)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * k + c + 10)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * k + c + 11)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * k + c + 12)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * k + c + 13)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * k + c + 14)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * k + c + 15)) rk) /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * (k + 1)
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb)])`,
  REWRITE_TAC[KEY_SPLIT] THEN
  (* Drive the 308-instruction drain with the extended-guard stepper         *)
  (* NSTEP_GP (it protects Q17..Q21, so the reduce's mid accumulator v18     *)
  (* stays unnormalised in both the pmull and the ext position), then        *)
  (* FINAL_STATE + REPEAT CONJ_TAC + the shape-routed dispatcher PP_DISPATCH *)
  (* (Q19 fold / Q30 counter / v0..v7 AES / ASM_REWRITE).                    *)
  REWRITE_TAC[htable_mem_8; htable_mem_4; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES_GCM_ENC_ALT_EXEC]
    (kterm `LENGTH tmc`)]) THEN
  MAP_EVERY NSTEP_GP (1--prepretail_steps) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN PP_DISPATCH);;

(* ========================================================================= *)
(* TAIL cascade: pc+0xee0 -> pc+0x1154.                                      *)
(*                                                                           *)
(* The tail handles the last r = nb - 8*g blocks (1 <= r <= 8), where 8*g    *)
(* blocks have been stored and GHASHed before it (g = k+1 after the          *)
(* prepretail, g = 0 after SETUP0).  Their keystreams are in Q0..Q7 at entry *)
(* (all AES rounds but the final rkn XOR).  It loads, encrypts and stores    *)
(* the r blocks, folds them into the GHASH accumulator Q19, does the final   *)
(* GF(2^128) reduce and the two memory writebacks:                           *)
(*      str q30,[x16]  -> ivec = word_reversefields 8 (ctr_block .. (nb+c))  *)
(*      st1 {v19},[x3] -> tag  = word_reversefields 8 (nist_ghash .. nb)     *)
(*                                                                           *)
(* At entry the remaining-bytes register x5 = X4 - X0 (sub x5,x4,x0 at       *)
(* 0xee4) is 16*r.  The cascade selects the arm: `cmp x5,#0x70` at 0xefc and *)
(* `b.gt` at 0x1424 take L256_enc_exact8_drain (0x1178) for r = 8, the       *)
(* `b.eq` at 0x142c takes L256_enc_rem2_drain (0x1434) for r = 2, and the    *)
(* other r slide through the cmp/b.gt chain from L256_enc_tail_slides        *)
(* (0xf08) to their entry: L256_enc_blocks_more_than_6/5/4 for r = 7/6/5,    *)
(* L256_enc_rem4_drain for r = 4, L256_enc_blocks_more_than_2 for r = 3 and  *)
(* L256_enc_blocks_less_than_1 for r = 1; r = 5..7 then finish on            *)
(* L256_enc_rem4_drain.  TAIL_REM1..TAIL_REM8 prove the arms and TAIL_REM    *)
(* combines them.  Every block is a full block: there is no                  *)
(* partial-block masking.                                                    *)
(*                                                                           *)
(* The Q19 fold is of the same kind as in PREPRETAIL and MAIN_LOOP           *)
(* (pmull/pmull2/eor3 Karatsuba over the fresh cipherblocks, then the        *)
(* reduce), so it reuses that machinery (NSTEP_GP, RECON_GRR, a              *)
(* Q19_FOLD_TAC-style fold).                                                 *)
(*                                                                           *)
(* The return value X0 = X9 = 16*nb (mov x0,x9 at 0x1154) is set by the      *)
(* epilogue: the tail ends at pc+0x1154 with X9 = word (16*nb), and the      *)
(* subroutine theorem, which also covers the epilogue, asserts the           *)
(* return value.                                                             *)
(* ========================================================================= *)

(* Eta/beta collapse for the accumulator-block (block-0) artifact.  The      *)
(* batched fold's block-0 index 8*g+0 reduces to 8*g, and higher-order       *)
(* matching in GHASH_POLYVAL_ACC_BATCHED leaves the `inblock` slot as a      *)
(* constant lambda `nist_cipher_block nonce rk (\x. inblock (8*g)) (8*g)`,   *)
(* beta-equal to the clean form but opaque to WORD_BITWISE_RULE (which       *)
(* cannot see through nist_cipher_block).  ETA_CONV does not apply (the      *)
(* lambda is constant, not \x. f x), so this targeted beta-collapse lemma is *)
(* used before the final AP_TERM.                                            *)
let NCB_ETA = prove
 (kterm `nist_cipher_block cipher c nonce rk (\x:num. inb (m:num)) m =
   nist_cipher_block cipher c nonce rk inb m`,
  REWRITE_TAC[nist_cipher_block; cipher_block] THEN CONV_TAC(DEPTH_CONV BETA_CONV));;

(* fold_q19_at lhs n tac: replace the assumption `lhs = <raw reduce>` by     *)
(* `lhs = nist_ghash .. (list_of_seq .. n)`, proving the equation between    *)
(* the two right-hand sides with tac (the arm's Q19 fold tactic).            *)
let fold_q19_at lhstm cnt foldtac : tactic =
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_eq c && lhs c = lhstm
    then TRANS th (prove
      (mk_eq(rhs c,
        vsubst [cnt, `n_blocks_fold:num`]
          (kterm `nist_ghash (cipher (word 0) rk) tag0
             (list_of_seq (nist_cipher_block cipher c nonce rk inblock) n_blocks_fold)`)),
       foldtac))
    else th);;

(* ========================================================================= *)
(* Tail cascade arm rem=1 (nblocks = 8*g+1), lands at 0x10f0                 *)
(* (L256_enc_blocks_less_than_1).                                            *)
(*                                                                           *)
(* One fresh block (8*g) is folded into the GHASH accumulator with a         *)
(* single-block APPEND (no batched reduce).  rem = 1 needs no Q18/Q27 pin.   *)
(*                                                                           *)
(* At the tail entry x5 = X4 - X0 = (in_p+16*nb) - (in_p+128*g) = 16*r       *)
(* (TAIL_X5_REM1..TAIL_X5_REM7, TAIL_X5_128_G); once it is rewritten to the  *)
(* literal, the stepper resolves the cmp/b.gt/b.eq cascade to the r arm with *)
(* concrete flags, so no separate branch-discharge lemma is needed.          *)
(* ========================================================================= *)

(* Fold `read Q19 s82` (the raw single-block reduce) to the compact          *)
(* nist_ghash..(8*g+1) in place, as TAIL_REM8's Q19 fold does.               *)
let FOLD_Q19_REM1 : tactic =
  fold_q19_at `read Q19 s82 : int128` `8 * g + 1` TAIL_Q19_FOLD_REM1;;

let AES_GCM_ENC_ALT_TAIL_REM1 = prove
 (kterm `!in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce c rk inblock nb g pc.
    nb = 8 * g + 1 /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (key_p, keybytes); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + pc_tail) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q28 s = word_reversefields 8 (EL nr rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 8)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c)) rk) /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (\s. read PC s = word (pc + pc_end) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; htable_mem_4; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES_GCM_ENC_ALT_EXEC]
    (kterm `LENGTH tmc`)]) THEN
  (* Assert the single tail input block; without this the plaintext load     *)
  (* stays a raw memory read and the whole ciphertext/GHASH chain drops.     *)
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g)`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g = 16 * (8 * g)`] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  (* Invert the keystream fact so that the ciphertext eor3 output is         *)
  (* state-independent.                                                      *)
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  (* Steps 1..9: the tail prefix (x5 = X4 - X0 at 0xee4); rewriting x5 to    *)
  (* word 16 lets the cascade resolve concretely to the rem = 1 arm          *)
  (* (L256_enc_blocks_less_than_1 at 0x10f0).                                *)
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAIL_X5_REM1]) THEN
  (* Steps 10..82: the cascade fall-through, the single-block fold and the   *)
  (* reduce, up to the final reduce eor3 at 0x1144 (s82: read Q19 = the raw  *)
  (* single-block reduce).                                                   *)
  MAP_EVERY NSTEP_GP (10--82) THEN
  (* Fold Q19 to the compact nist_ghash..(8*g+1) before ext/rev64/store      *)
  (* (otherwise the rev64 of the raw reduce grows very large), then drop the *)
  (* dead reduce scratch.                                                    *)
  FOLD_Q19_REM1 THEN
  DISCARD_DEAD_REDUCE_SCRATCH THEN
  (* Steps 83..85: ext, rev64 and st1 (tag) at 0x1148/0x114c/0x1150; the PC  *)
  (* is then pc+0x1154.                                                      *)
  MAP_EVERY NSTEP_GP (83--85) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (* ivec store: 7 `sub v30` in the cascade take 8g+c+8 to 8g+c+1 = nb+c. *)
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word_sub (word_sub (word_sub (word_sub (word_sub (word_sub
        (word (8 * g + c + 8):int32) (word 1)) (word 1)) (word 1)) (word 1))
        (word 1)) (word 1)) (word 1) = word (8 * g + c + 1)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  (* tag store: read(tag_p) = rev8 (nist_ghash..nb), Q19 being folded. *)
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 1` THEN ARITH_TAC;
    ALL_TAC] THEN
  (* out-forall (j < nb): the old blocks j < 8*g via the incoming            *)
  (* out-forall; the one new block j = 8*g via the retained ciphertext store *)
  (* and the double-rkn cancellation.                                        *)
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 1 <=> j < 8 * g \/ j = 8 * g`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[aes_ctr_block] THEN REWRITE_TAC[ARITH_RULE `8 * g + c = c + 8 * g`] THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* ========================================================================= *)
(* Tail cascade arm rem=2 (nblocks = 8*g+2), lands at 0x1434                 *)
(* (L256_enc_rem2_drain).                                                    *)
(*                                                                           *)
(* The second remainder-cascade arm.  It folds two fresh blocks (8*g and     *)
(* 8*g+1) into the GHASH accumulator with a 2-block batched reduce           *)
(* (GHASH_POLYVAL_ACC_BATCHED), where rem = 1 uses a single-block APPEND.    *)
(* Like the arms for rem = 3..7, its precondition also pins the entry value  *)
(* of Q27 (q27_init).                                                        *)
(* ========================================================================= *)

(* Two-block Q19 fold: RECON_GRR exposes the reduce; the 2 blocks normalise  *)
(* to nist_cipher_block(8*g),(8*g+1); GHASH_REDUCE_RAW_XOR +                 *)
(* KARATSUBA_IS_DOT_HW + KDOT_B0 (block 0 carries the accumulator, with the  *)
(* store-order byteswap) collapse the summed lanes to                        *)
(*      word_xor (polyval_dot cb(8*g+1) H^0)                                 *)
(*               (polyval_dot (sofar (x) cb(8*g)) H^1)                       *)
(* which is exactly GHASH_POLYVAL_ACC_BATCHED with bs = [cb(8*g+1)], b =     *)
(* cb(8*g), a = sofar; the RHS nist_ghash..(8*g+2) unfolds to the same via   *)
(* NIST_GHASH_IS_POLYVAL + list_of_seq/APPEND/GHASH_ACC_APPEND + the batched *)
(* lemma.  Only block 8*g+1's counter 8*g+c+1 needs reindexing to (8*g+1)+c; *)
(* block 8*g's counter 8*g+c already has that shape.                         *)
let TAIL_Q19_FOLD_REM2 =
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
  REWRITE_TAC[ARITH_RULE `8 * g + c + 1 = (8 * g + 1) + c`] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN
  REWRITE_TAC[GSYM cipher_block] THEN REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_XOR] THEN
  REWRITE_TAC[KARATSUBA_IS_DOT_HW] THEN
  REWRITE_TAC[KDOT_B0] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `8 * g + 2 = SUC(SUC(8 * g))`;
              ARITH_RULE `2 + 8 * g = SUC(SUC(8 * g))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  MP_TAC(ISPECL
    [kterm `ghash_twist (cipher (word 0) rk)`;
     kterm `[nist_cipher_block cipher c nonce rk inblock (8*g+1)]:(int128)list`;
     kterm `ghash_polyval_acc (ghash_twist (cipher (word 0) rk)) tag0
        (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8*g))`;
     kterm `nist_cipher_block cipher c nonce rk inblock (8*g)`]
    GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ADD_0] THEN
  REWRITE_TAC[polyval_dot] THEN
  REWRITE_TAC[GSYM PROP3_XOR] THEN
  REWRITE_TAC[NCB_ETA] THEN
  REWRITE_TAC[ARITH_RULE `1 + 8 * g = 8 * g + 1`] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;;

(* Fold `read Q19 s53` (the raw 2-block reduce) to the compact               *)
(* nist_ghash..(8*g+2) in place, before ext/rev64/store (as FOLD_Q19_REM1).  *)
let FOLD_Q19_REM2 : tactic =
  fold_q19_at `read Q19 s53 : int128` `8 * g + 2` TAIL_Q19_FOLD_REM2;;

let AES_GCM_ENC_ALT_TAIL_REM2 = prove
 (kterm `!q27_init in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce c rk inblock nb g pc.
    nb = 8 * g + 2 /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (key_p, keybytes); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + pc_tail) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q27 s = q27_init /\
           read Q28 s = word_reversefields 8 (EL nr rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 8)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 2)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 3)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 4)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 5)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 6)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 7)) rk) /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (\s. read PC s = word (pc + pc_end) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; htable_mem_4; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES_GCM_ENC_ALT_EXEC]
    (kterm `LENGTH tmc`)]) THEN
  (* Assert the 2 tail input blocks; without this the plaintext loads stay   *)
  (* raw memory reads and the ciphertext/GHASH chain drops.                  *)
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 16)))) s0 =
    inblock (8 * g + 1)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g + 16 = 16 * (8 * g + 1)`] THEN
    REWRITE_TAC[ARITH_RULE `128 * g = 16 * (8 * g)`] THEN
    CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  (* Invert the keystream facts so that the ciphertext eor3 outputs are      *)
  (* state-independent.                                                      *)
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  (* Steps 1..9: the tail prefix; rewriting x5 to word 32 lets the cascade   *)
  (* resolve concretely to the rem = 2 arm (b.eq at 0x142c -> 0x1434).       *)
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAIL_X5_REM2]) THEN
  (* Steps 10..53: the dispatch and the 2-block drain, up to the final       *)
  (* reduce eor3 at 0x14d0 (s53: read Q19 = the raw 2-block reduce).         *)
  MAP_EVERY NSTEP_GP (10--53) THEN
  (* Fold Q19 to the compact nist_ghash..(8*g+2) before ext/rev64/store,     *)
  (* then drop the dead reduce scratch.                                      *)
  FOLD_Q19_REM2 THEN
  DISCARD_DEAD_REDUCE_SCRATCH THEN
  (* Steps 54..57: ext, rev64 and st1 (tag) at 0x14d4/0x14d8/0x14dc, then    *)
  (* the b at 0x14e0 to pc+0x1154.                                           *)
  MAP_EVERY NSTEP_GP (54--57) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (* ivec store: 6 `sub v30` in the drain take 8g+c+8 to 8g+c+2 = nb+c. *)
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word_sub (word_sub (word_sub (word_sub (word_sub
        (word (8 * g + c + 8):int32) (word 1)) (word 1)) (word 1)) (word 1))
        (word 1)) (word 1) = word (8 * g + c + 2)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  (* tag store: read(tag_p) = rev8 (nist_ghash..nb), Q19 being folded. *)
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 2` THEN ARITH_TAC;
    ALL_TAC] THEN
  (* out-forall (j < nb): the old blocks j < 8*g via the incoming            *)
  (* out-forall; the 2 new blocks j = 8*g, 8*g+1 via the retained ciphertext *)
  (* stores and the double-rkn cancellation.                                 *)
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 2 <=>
                       j < 8 * g \/ j = 8 * g \/ j = 8 * g + 1`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rkn = word_xor ch (word_xor rkn inb)`] THEN
  REWRITE_TAC[XOR_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `8 * g + c = c + 8 * g`] THEN
  REWRITE_TAC[ADD_ASSOC] THEN
  REWRITE_TAC[ARITH_RULE `1 + c = c + 1`; ARITH_RULE `2 + c = c + 2`;
              ARITH_RULE `3 + c = c + 3`; ARITH_RULE `4 + c = c + 4`;
              ARITH_RULE `5 + c = c + 5`; ARITH_RULE `6 + c = c + 6`;
              ARITH_RULE `7 + c = c + 7`] THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* ========================================================================= *)
(* FAST2_TAIL: the nb = 2 (32-byte) small-path tail, from pc+0x17d4 (the     *)
(* small_2 tail start, after the L256_enc_small_2 AES loop and the rkn       *)
(* load) to pc+0x1154.  The two keystreams are in Q0/Q1 (up to the final     *)
(* rkn XOR, with rkn in Q28), Q12 holds the tbl byte-reverse index and Q30   *)
(* enters as ctr(c+nb) (= 8g+c+2).  The leg loads, encrypts and stores the   *)
(* two blocks, folds them into Q19 (at s39, with TAIL_Q19_FOLD_REM2) and     *)
(* finishes in L256_enc_small_reduce with the tbl/st1 tag store              *)
(* (steps 40-42).                                                            *)
(* ========================================================================= *)
let AES_GCM_ENC_ALT_FAST2_TAIL = prove
 (kterm `!in_p out_p tag_p ivec_p htable_p mod_p
     tag0 nonce c rk inblock nb g pc.
    nb = 8 * g + 2 /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + pc_fast2) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X16 s = ivec_p /\
           read Q12 s = word 0x000102030405060708090a0b0c0d0e0f /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           word_xor (read Q0 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * g + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * g + c + 1)) rk) /\
           read Q19 s =
             nist_ghash (cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8 * g)) /\
           read Q28 s = word_reversefields 8 (EL nr rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 2)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (\s. read PC s = word (pc + pc_end) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; htable_mem_4; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES_GCM_ENC_ALT_EXEC]
    (kterm `LENGTH tmc`)]) THEN
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 16)))) s0 =
    inblock (8 * g + 1)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g + 16 = 16 * (8 * g + 1)`] THEN
    REWRITE_TAC[ARITH_RULE `128 * g = 16 * (8 * g)`] THEN
    CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  MAP_EVERY NSTEP_GP (1--39) THEN
  fold_q19_at `read Q19 s39 : int128` `8 * g + 2` TAIL_Q19_FOLD_REM2 THEN
  (* Q12 is the live tbl index here, not reduce scratch: keep it, so that    *)
  (* read Q12 reaches the tbl step.                                          *)
  DISCARD_REGS ["Q17";"Q18";"Q20";"Q21";"Q22";"Q23";"Q24";"Q25";"Q26";"Q29";"Q16";"Q8";"Q9";"Q10";"Q11";"Q13";"Q14";"Q15"] THEN
  MAP_EVERY NSTEP_GP (40--42) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word_sub (word_sub (word_sub (word_sub (word_sub
        (word (8 * g + 10):int32) (word 1)) (word 1)) (word 1)) (word 1))
        (word 1)) (word 1) = word (8 * g + 4)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   (* With the concrete index in Q12, tbl expands to the same word_join byte *)
   (* reversal as ext+rev64, so TAG_STORE_REV64 applies.                     *)
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 2` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 2 <=>
                       j < 8 * g \/ j = 8 * g \/ j = 8 * g + 1`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rkn = word_xor ch (word_xor rkn inb)`] THEN
  REWRITE_TAC[XOR_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `8 * g + c = c + 8 * g`] THEN
  REWRITE_TAC[ADD_ASSOC] THEN
  REWRITE_TAC[ARITH_RULE `1 + c = c + 1`; ARITH_RULE `2 + c = c + 2`;
              ARITH_RULE `3 + c = c + 3`; ARITH_RULE `4 + c = c + 4`;
              ARITH_RULE `5 + c = c + 5`; ARITH_RULE `6 + c = c + 6`;
              ARITH_RULE `7 + c = c + 7`] THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* ========================================================================= *)
(* FAST1_TAIL: the nb = 1 (16-byte) small-path tail, the one-block version   *)
(* of FAST2_TAIL (keystream Q0 only; the same tbl tag store, with Q12 the    *)
(* index).  Entry 0x187c (the small_1 tail start: ldr q8; ext v16; mov v29;  *)
(* eor3 v9), then the single-block drain and L256_enc_small_reduce.  Q30     *)
(* enters as ctr(c+nb) (= 8g+c+1), built directly by the small_1 code.  Q19  *)
(* folds at s24.                                                             *)
(* ========================================================================= *)
let AES_GCM_ENC_ALT_FAST1_TAIL = prove
 (kterm `!in_p out_p tag_p ivec_p htable_p mod_p
     tag0 nonce c rk inblock nb g pc.
    nb = 8 * g + 1 /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + pc_fast1) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X16 s = ivec_p /\
           read Q12 s = word 0x000102030405060708090a0b0c0d0e0f /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           word_xor (read Q0 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * g + c)) rk) /\
           read Q19 s =
             nist_ghash (cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8 * g)) /\
           read Q28 s = word_reversefields 8 (EL nr rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 1)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (\s. read PC s = word (pc + pc_end) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; htable_mem_4; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES_GCM_ENC_ALT_EXEC]
    (kterm `LENGTH tmc`)]) THEN
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g)`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g = 16 * (8 * g)`] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  MAP_EVERY NSTEP_GP (1--24) THEN
  fold_q19_at `read Q19 s24 : int128` `8 * g + 1` TAIL_Q19_FOLD_REM1 THEN
  DISCARD_REGS ["Q17";"Q18";"Q20";"Q21";"Q22";"Q23";"Q24";"Q25";"Q26";"Q29";"Q16";"Q8";"Q9";"Q10";"Q11";"Q13";"Q14";"Q15"] THEN
  MAP_EVERY NSTEP_GP (25--27) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word_sub (word_sub (word_sub (word_sub (word_sub (word_sub
        (word (8 * g + 10):int32) (word 1)) (word 1)) (word 1)) (word 1))
        (word 1)) (word 1)) (word 1) = word (8 * g + 3)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 1` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 1 <=>
                       j < 8 * g \/ j = 8 * g`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rkn = word_xor ch (word_xor rkn inb)`] THEN
  REWRITE_TAC[XOR_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `8 * g + c = c + 8 * g`] THEN
  REWRITE_TAC[ADD_ASSOC] THEN
  REWRITE_TAC[ARITH_RULE `1 + c = c + 1`; ARITH_RULE `2 + c = c + 2`;
              ARITH_RULE `3 + c = c + 3`; ARITH_RULE `4 + c = c + 4`;
              ARITH_RULE `5 + c = c + 5`; ARITH_RULE `6 + c = c + 6`;
              ARITH_RULE `7 + c = c + 7`] THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* ========================================================================= *)
(* Tail cascade arm rem=3 (nblocks = 8*g+3), lands at 0x1070.                *)
(* 3-block batched Q19 fold; Q27 pinned (q27_init).  5 `sub v30` decrements  *)
(* roll the counter 8g+c+8 -> 8g+c+3 = nb+c.                                 *)
(* ========================================================================= *)

let TAIL_Q19_FOLD_REM3 =
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
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [ARITH_RULE `8 * g + c + 1 = (8 * g + 1) + c`;
     ARITH_RULE `8 * g + c + 2 = (8 * g + 2) + c`] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN
  REWRITE_TAC[GSYM cipher_block] THEN REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_XOR] THEN
  REWRITE_TAC[KARATSUBA_IS_DOT_HW] THEN
  REWRITE_TAC[KDOT_B0] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `8 * g + 3 = SUC(SUC(SUC(8 * g)))`;
              ARITH_RULE `3 + 8 * g = SUC(SUC(SUC(8 * g)))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  MP_TAC(ISPECL
    [kterm `ghash_twist (cipher (word 0) rk)`;
     kterm `[nist_cipher_block cipher c nonce rk inblock (8*g+1);
       nist_cipher_block cipher c nonce rk inblock (8*g+2)]:(int128)list`;
     kterm `ghash_polyval_acc (ghash_twist (cipher (word 0) rk)) tag0
        (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8*g))`;
     kterm `nist_cipher_block cipher c nonce rk inblock (8*g)`]
    GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ADD_0] THEN
  REWRITE_TAC[polyval_dot] THEN
  REWRITE_TAC[GSYM PROP3_XOR] THEN
  REWRITE_TAC[NCB_ETA] THEN
  REWRITE_TAC[ARITH_RULE `1 + 8 * g = 8 * g + 1`; ARITH_RULE `2 + 8 * g = 8 * g + 2`] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;;

let FOLD_Q19_REM3 : tactic =
  fold_q19_at `read Q19 s107 : int128` `8 * g + 3` TAIL_Q19_FOLD_REM3;;

let AES_GCM_ENC_ALT_TAIL_REM3 = prove
 (kterm `!q27_init in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce c rk inblock nb g pc.
    nb = 8 * g + 3 /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (key_p, keybytes); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + pc_tail) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q27 s = q27_init /\
           read Q28 s = word_reversefields 8 (EL nr rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 8)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 2)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 3)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 4)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 5)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 6)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 7)) rk) /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (\s. read PC s = word (pc + pc_end) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; htable_mem_4; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES_GCM_ENC_ALT_EXEC]
    (kterm `LENGTH tmc`)]) THEN
  SUBGOAL_THEN
   `    read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 16)))) s0 =
    inblock (8 * g + 1) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 32)))) s0 =
    inblock (8 * g + 2)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g = 16 * (8 * g)`;
      ARITH_RULE `128 * g + 16 = 16 * (8 * g + 1)`;
      ARITH_RULE `128 * g + 32 = 16 * (8 * g + 2)`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAIL_X5_REM3]) THEN
  MAP_EVERY NSTEP_GP (10--107) THEN
  FOLD_Q19_REM3 THEN
  DISCARD_DEAD_REDUCE_SCRATCH THEN
  MAP_EVERY NSTEP_GP (108--110) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word_sub (word_sub (word_sub (word_sub (word (8 * g + c + 8):int32) (word 1)) (word 1)) (word 1)) (word 1)) (word 1) = word (8 * g + c + 3)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 3` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 3 <=>
                       j < 8 * g \/ j = 8 * g \/ j = 8 * g + 1 \/ j = 8 * g + 2`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rkn = word_xor ch (word_xor rkn inb)`] THEN
  REWRITE_TAC[XOR_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `8 * g + c = c + 8 * g`] THEN
  REWRITE_TAC[ADD_ASSOC] THEN
  REWRITE_TAC[ARITH_RULE `1 + c = c + 1`; ARITH_RULE `2 + c = c + 2`;
              ARITH_RULE `3 + c = c + 3`; ARITH_RULE `4 + c = c + 4`;
              ARITH_RULE `5 + c = c + 5`; ARITH_RULE `6 + c = c + 6`;
              ARITH_RULE `7 + c = c + 7`] THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* ========================================================================= *)
(* Tail cascade arm rem=4 (nblocks = 8*g+4), lands at 0x1328.                *)
(* 4-block batched Q19 fold; Q27 pinned (q27_init).  4 `sub v30` decrements  *)
(* roll the counter 8g+c+8 -> 8g+c+4 = nb+c.                                 *)
(* ========================================================================= *)

let TAIL_Q19_FOLD_REM4 =
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
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [ARITH_RULE `8 * g + c + 1 = (8 * g + 1) + c`;
     ARITH_RULE `8 * g + c + 2 = (8 * g + 2) + c`;
     ARITH_RULE `8 * g + c + 3 = (8 * g + 3) + c`] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN
  REWRITE_TAC[GSYM cipher_block] THEN REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_XOR] THEN
  REWRITE_TAC[KARATSUBA_IS_DOT_HW] THEN
  REWRITE_TAC[KDOT_B0] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `8 * g + 4 = SUC(SUC(SUC(SUC(8 * g))))`;
              ARITH_RULE `4 + 8 * g = SUC(SUC(SUC(SUC(8 * g))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  MP_TAC(ISPECL
    [kterm `ghash_twist (cipher (word 0) rk)`;
     kterm `[nist_cipher_block cipher c nonce rk inblock (8*g+1);
       nist_cipher_block cipher c nonce rk inblock (8*g+2);
       nist_cipher_block cipher c nonce rk inblock (8*g+3)]:(int128)list`;
     kterm `ghash_polyval_acc (ghash_twist (cipher (word 0) rk)) tag0
        (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8*g))`;
     kterm `nist_cipher_block cipher c nonce rk inblock (8*g)`]
    GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ADD_0] THEN
  REWRITE_TAC[polyval_dot] THEN
  REWRITE_TAC[GSYM PROP3_XOR] THEN
  REWRITE_TAC[NCB_ETA] THEN
  REWRITE_TAC[ARITH_RULE `1 + 8 * g = 8 * g + 1`; ARITH_RULE `2 + 8 * g = 8 * g + 2`; ARITH_RULE `3 + 8 * g = 8 * g + 3`] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;;

let FOLD_Q19_REM4 : tactic =
  fold_q19_at `read Q19 s106 : int128` `8 * g + 4` TAIL_Q19_FOLD_REM4;;

let AES_GCM_ENC_ALT_TAIL_REM4 = prove
 (kterm `!q27_init in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce c rk inblock nb g pc.
    nb = 8 * g + 4 /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (key_p, keybytes); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + pc_tail) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q27 s = q27_init /\
           read Q28 s = word_reversefields 8 (EL nr rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 8)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 2)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 3)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 4)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 5)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 6)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 7)) rk) /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (\s. read PC s = word (pc + pc_end) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; htable_mem_4; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES_GCM_ENC_ALT_EXEC]
    (kterm `LENGTH tmc`)]) THEN
  SUBGOAL_THEN
   `    read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 16)))) s0 =
    inblock (8 * g + 1) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 32)))) s0 =
    inblock (8 * g + 2) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 48)))) s0 =
    inblock (8 * g + 3)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g = 16 * (8 * g)`;
      ARITH_RULE `128 * g + 16 = 16 * (8 * g + 1)`;
      ARITH_RULE `128 * g + 32 = 16 * (8 * g + 2)`;
      ARITH_RULE `128 * g + 48 = 16 * (8 * g + 3)`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAIL_X5_REM4]) THEN
  MAP_EVERY NSTEP_GP (10--106) THEN
  FOLD_Q19_REM4 THEN
  DISCARD_DEAD_REDUCE_SCRATCH THEN
  MAP_EVERY NSTEP_GP (107--110) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word_sub (word_sub (word_sub (word (8 * g + c + 8):int32) (word 1)) (word 1)) (word 1)) (word 1) = word (8 * g + c + 4)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 4` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 4 <=>
                       j < 8 * g \/ j = 8 * g \/ j = 8 * g + 1 \/ j = 8 * g + 2 \/ j = 8 * g + 3`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rkn = word_xor ch (word_xor rkn inb)`] THEN
  REWRITE_TAC[XOR_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `8 * g + c = c + 8 * g`] THEN
  REWRITE_TAC[ADD_ASSOC] THEN
  REWRITE_TAC[ARITH_RULE `1 + c = c + 1`; ARITH_RULE `2 + c = c + 2`;
              ARITH_RULE `3 + c = c + 3`; ARITH_RULE `4 + c = c + 4`;
              ARITH_RULE `5 + c = c + 5`; ARITH_RULE `6 + c = c + 6`;
              ARITH_RULE `7 + c = c + 7`] THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* ========================================================================= *)
(* FAST4_TAIL: the nb = 4 (64-byte) small-path tail.  Entry pc+0x15ac (the   *)
(* small_4 tail start) with the 4 keystreams (Q0..Q3) as preconditions (a    *)
(* fresh entry, so that the tail's eor3 write of the block-0 ciphertext is   *)
(* tracked, as in FAST2_TAIL); the tail start (block-0 plaintext load, eor3  *)
(* ciphertext write, accumulator reset) runs into the eor3-fused 4-block     *)
(* drain and L256_enc_small_reduce, ending at pc+0x1154.  Q30 enters as      *)
(* ctr(c+nb) (= 8g+c+4), built directly by the small_4 code.  Q19 folds      *)
(* at s67.                                                                   *)
(* ========================================================================= *)

let FOLD_Q19_REM4_FAST4 : tactic =
  fold_q19_at `read Q19 s67 : int128` `8 * g + 4` TAIL_Q19_FOLD_REM4;;

let AES_GCM_ENC_ALT_FAST4_TAIL = prove
 (kterm `!in_p out_p tag_p ivec_p htable_p mod_p
     tag0 nonce c rk inblock nb g pc.
    nb = 8 * g + 4 /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + pc_fast4) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X16 s = ivec_p /\
           read Q12 s = word 0x000102030405060708090a0b0c0d0e0f /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           word_xor (read Q0 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * g + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * g + c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * g + c + 2)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * g + c + 3)) rk) /\
           read Q19 s =
             nist_ghash (cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8 * g)) /\
           read Q28 s = word_reversefields 8 (EL nr rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 4)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (\s. read PC s = word (pc + pc_end) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; htable_mem_4; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES_GCM_ENC_ALT_EXEC]
    (kterm `LENGTH tmc`)]) THEN
  SUBGOAL_THEN
   `    read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 16)))) s0 =
    inblock (8 * g + 1) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 32)))) s0 =
    inblock (8 * g + 2) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 48)))) s0 =
    inblock (8 * g + 3)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g = 16 * (8 * g)`;
      ARITH_RULE `128 * g + 16 = 16 * (8 * g + 1)`;
      ARITH_RULE `128 * g + 32 = 16 * (8 * g + 2)`;
      ARITH_RULE `128 * g + 48 = 16 * (8 * g + 3)`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  MAP_EVERY NSTEP_GP (1--67) THEN
  FOLD_Q19_REM4_FAST4 THEN
  (* Q12 is the live tbl index: discard DISCARD_DEAD_REDUCE_SCRATCH's        *)
  (* registers except Q12.                                                   *)
  DISCARD_REGS ["Q17"; "Q18"; "Q20"; "Q21"; "Q22"; "Q23"; "Q24"; "Q25"; "Q26";
     "Q29"; "Q16"; "Q8"; "Q9"; "Q10"; "Q11"; "Q13"; "Q14"; "Q15"] THEN
  MAP_EVERY NSTEP_GP (68--70) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word_sub (word_sub (word_sub (word (8 * g + 10):int32) (word 1)) (word 1)) (word 1)) (word 1) = word (8 * g + 6)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 4` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 4 <=>
                       j < 8 * g \/ j = 8 * g \/ j = 8 * g + 1 \/ j = 8 * g + 2 \/ j = 8 * g + 3`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rkn = word_xor ch (word_xor rkn inb)`] THEN
  REWRITE_TAC[XOR_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `8 * g + c = c + 8 * g`] THEN
  REWRITE_TAC[ADD_ASSOC] THEN
  REWRITE_TAC[ARITH_RULE `1 + c = c + 1`; ARITH_RULE `2 + c = c + 2`;
              ARITH_RULE `3 + c = c + 3`; ARITH_RULE `4 + c = c + 4`;
              ARITH_RULE `5 + c = c + 5`; ARITH_RULE `6 + c = c + 6`;
              ARITH_RULE `7 + c = c + 7`] THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* ========================================================================= *)
(* FAST3_TAIL: the nb = 3 (48-byte) small-path tail, the three-block version *)
(* of FAST4_TAIL (keystreams Q0, Q1, Q2; the same tbl tag store, with Q12    *)
(* the index).  Entry 0x16ec (the small_3 tail start), then the eor3-fused   *)
(* 3-block drain and L256_enc_small_reduce.  Q30 enters as ctr(c+nb) (=      *)
(* 8g+c+3), built directly by the small_3 code.  Q19 folds at s50 (with the  *)
(* cascade's TAIL_Q19_FOLD_REM3).                                            *)
(* ========================================================================= *)
let AES_GCM_ENC_ALT_FAST3_TAIL = prove
 (kterm `!in_p out_p tag_p ivec_p htable_p mod_p
     tag0 nonce c rk inblock nb g pc.
    nb = 8 * g + 3 /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + pc_fast3) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X16 s = ivec_p /\
           read Q12 s = word 0x000102030405060708090a0b0c0d0e0f /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           word_xor (read Q0 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * g + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * g + c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * g + c + 2)) rk) /\
           read Q19 s =
             nist_ghash (cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8 * g)) /\
           read Q28 s = word_reversefields 8 (EL nr rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 3)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (\s. read PC s = word (pc + pc_end) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; htable_mem_4; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES_GCM_ENC_ALT_EXEC]
    (kterm `LENGTH tmc`)]) THEN
  SUBGOAL_THEN
   `    read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 16)))) s0 =
    inblock (8 * g + 1) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 32)))) s0 =
    inblock (8 * g + 2)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g = 16 * (8 * g)`;
      ARITH_RULE `128 * g + 16 = 16 * (8 * g + 1)`;
      ARITH_RULE `128 * g + 32 = 16 * (8 * g + 2)`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  MAP_EVERY NSTEP_GP (1--50) THEN
  fold_q19_at `read Q19 s50 : int128` `8 * g + 3` TAIL_Q19_FOLD_REM3 THEN
  DISCARD_REGS ["Q17"; "Q18"; "Q20"; "Q21"; "Q22"; "Q23"; "Q24"; "Q25"; "Q26";
     "Q29"; "Q16"; "Q8"; "Q9"; "Q10"; "Q11"; "Q13"; "Q14"; "Q15";
     "Q3"; "Q4"; "Q5"] THEN
  MAP_EVERY NSTEP_GP (51--53) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word_sub (word_sub (word_sub (word_sub
        (word (8 * g + 10):int32) (word 1)) (word 1)) (word 1)) (word 1))
        (word 1) = word (8 * g + 5)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 3` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 3 <=>
                       j < 8 * g \/ j = 8 * g \/ j = 8 * g + 1 \/ j = 8 * g + 2`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rkn = word_xor ch (word_xor rkn inb)`] THEN
  REWRITE_TAC[XOR_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `8 * g + c = c + 8 * g`] THEN
  REWRITE_TAC[ADD_ASSOC] THEN
  REWRITE_TAC[ARITH_RULE `1 + c = c + 1`; ARITH_RULE `2 + c = c + 2`;
              ARITH_RULE `3 + c = c + 3`; ARITH_RULE `4 + c = c + 4`;
              ARITH_RULE `5 + c = c + 5`; ARITH_RULE `6 + c = c + 6`;
              ARITH_RULE `7 + c = c + 7`] THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* ========================================================================= *)
(* Tail cascade arm rem=5 (nblocks = 8*g+5), lands at 0x1034.                *)
(* 5-block batched Q19 fold; Q27 pinned (q27_init).  3 `sub v30` decrements  *)
(* roll the counter 8g+c+8 -> 8g+c+5 = nb+c.                                 *)
(* ========================================================================= *)

let TAIL_Q19_FOLD_REM5 =
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
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [ARITH_RULE `8 * g + c + 1 = (8 * g + 1) + c`;
     ARITH_RULE `8 * g + c + 2 = (8 * g + 2) + c`;
     ARITH_RULE `8 * g + c + 3 = (8 * g + 3) + c`;
     ARITH_RULE `8 * g + c + 4 = (8 * g + 4) + c`] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN
  REWRITE_TAC[GSYM cipher_block] THEN REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_XOR] THEN
  REWRITE_TAC[KARATSUBA_IS_DOT_HW] THEN
  REWRITE_TAC[KDOT_B0] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `8 * g + 5 = SUC(SUC(SUC(SUC(SUC(8 * g)))))`;
              ARITH_RULE `5 + 8 * g = SUC(SUC(SUC(SUC(SUC(8 * g)))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  MP_TAC(ISPECL
    [kterm `ghash_twist (cipher (word 0) rk)`;
     kterm `[nist_cipher_block cipher c nonce rk inblock (8*g+1);
       nist_cipher_block cipher c nonce rk inblock (8*g+2);
       nist_cipher_block cipher c nonce rk inblock (8*g+3);
       nist_cipher_block cipher c nonce rk inblock (8*g+4)]:(int128)list`;
     kterm `ghash_polyval_acc (ghash_twist (cipher (word 0) rk)) tag0
        (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8*g))`;
     kterm `nist_cipher_block cipher c nonce rk inblock (8*g)`]
    GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ADD_0] THEN
  REWRITE_TAC[polyval_dot] THEN
  REWRITE_TAC[GSYM PROP3_XOR] THEN
  REWRITE_TAC[NCB_ETA] THEN
  REWRITE_TAC[ARITH_RULE `1 + 8 * g = 8 * g + 1`; ARITH_RULE `2 + 8 * g = 8 * g + 2`; ARITH_RULE `3 + 8 * g = 8 * g + 3`; ARITH_RULE `4 + 8 * g = 8 * g + 4`] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;;

let FOLD_Q19_REM5 : tactic =
  (* rem = 5 finishes on the eor3-fused rem4_drain, entered at step 57; its
     final reduce eor3 at 0x1410 is step 115 (57 + 58), so Q19 is folded
     at s115. *)
  fold_q19_at `read Q19 s115 : int128` `8 * g + 5` TAIL_Q19_FOLD_REM5;;

let AES_GCM_ENC_ALT_TAIL_REM5 = prove
 (kterm `!q27_init in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce c rk inblock nb g pc.
    nb = 8 * g + 5 /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (key_p, keybytes); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + pc_tail) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q27 s = q27_init /\
           read Q28 s = word_reversefields 8 (EL nr rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 8)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 2)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 3)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 4)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 5)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 6)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 7)) rk) /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (\s. read PC s = word (pc + pc_end) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; htable_mem_4; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES_GCM_ENC_ALT_EXEC]
    (kterm `LENGTH tmc`)]) THEN
  SUBGOAL_THEN
   `    read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 16)))) s0 =
    inblock (8 * g + 1) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 32)))) s0 =
    inblock (8 * g + 2) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 48)))) s0 =
    inblock (8 * g + 3) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 64)))) s0 =
    inblock (8 * g + 4)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g = 16 * (8 * g)`;
      ARITH_RULE `128 * g + 16 = 16 * (8 * g + 1)`;
      ARITH_RULE `128 * g + 32 = 16 * (8 * g + 2)`;
      ARITH_RULE `128 * g + 48 = 16 * (8 * g + 3)`;
      ARITH_RULE `128 * g + 64 = 16 * (8 * g + 4)`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAIL_X5_REM5]) THEN
  MAP_EVERY NSTEP_GP (10--115) THEN
  FOLD_Q19_REM5 THEN
  DISCARD_DEAD_REDUCE_SCRATCH THEN
  MAP_EVERY NSTEP_GP (116--119) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word_sub (word_sub (word (8 * g + c + 8):int32) (word 1)) (word 1)) (word 1) = word (8 * g + c + 5)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 5` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 5 <=>
                       j < 8 * g \/ j = 8 * g \/ j = 8 * g + 1 \/ j = 8 * g + 2 \/ j = 8 * g + 3 \/ j = 8 * g + 4`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rkn = word_xor ch (word_xor rkn inb)`] THEN
  REWRITE_TAC[XOR_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `8 * g + c = c + 8 * g`] THEN
  REWRITE_TAC[ADD_ASSOC] THEN
  REWRITE_TAC[ARITH_RULE `1 + c = c + 1`; ARITH_RULE `2 + c = c + 2`;
              ARITH_RULE `3 + c = c + 3`; ARITH_RULE `4 + c = c + 4`;
              ARITH_RULE `5 + c = c + 5`; ARITH_RULE `6 + c = c + 6`;
              ARITH_RULE `7 + c = c + 7`] THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* ========================================================================= *)
(* Tail cascade arm rem=6 (nblocks = 8*g+6), lands at 0xff8.                 *)
(* 6-block batched Q19 fold; Q27 pinned (q27_init).  2 `sub v30` decrements  *)
(* roll the counter 8g+c+8 -> 8g+c+6 = nb+c.                                 *)
(* ========================================================================= *)

let TAIL_Q19_FOLD_REM6 =
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
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [ARITH_RULE `8 * g + c + 1 = (8 * g + 1) + c`;
     ARITH_RULE `8 * g + c + 2 = (8 * g + 2) + c`;
     ARITH_RULE `8 * g + c + 3 = (8 * g + 3) + c`;
     ARITH_RULE `8 * g + c + 4 = (8 * g + 4) + c`;
     ARITH_RULE `8 * g + c + 5 = (8 * g + 5) + c`] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN
  REWRITE_TAC[GSYM cipher_block] THEN REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_XOR] THEN
  REWRITE_TAC[KARATSUBA_IS_DOT_HW] THEN
  REWRITE_TAC[KDOT_B0] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `8 * g + 6 = SUC(SUC(SUC(SUC(SUC(SUC(8 * g))))))`;
              ARITH_RULE `6 + 8 * g = SUC(SUC(SUC(SUC(SUC(SUC(8 * g))))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  MP_TAC(ISPECL
    [kterm `ghash_twist (cipher (word 0) rk)`;
     kterm `[nist_cipher_block cipher c nonce rk inblock (8*g+1);
       nist_cipher_block cipher c nonce rk inblock (8*g+2);
       nist_cipher_block cipher c nonce rk inblock (8*g+3);
       nist_cipher_block cipher c nonce rk inblock (8*g+4);
       nist_cipher_block cipher c nonce rk inblock (8*g+5)]:(int128)list`;
     kterm `ghash_polyval_acc (ghash_twist (cipher (word 0) rk)) tag0
        (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8*g))`;
     kterm `nist_cipher_block cipher c nonce rk inblock (8*g)`]
    GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ADD_0] THEN
  REWRITE_TAC[polyval_dot] THEN
  REWRITE_TAC[GSYM PROP3_XOR] THEN
  REWRITE_TAC[NCB_ETA] THEN
  REWRITE_TAC[ARITH_RULE `1 + 8 * g = 8 * g + 1`; ARITH_RULE `2 + 8 * g = 8 * g + 2`; ARITH_RULE `3 + 8 * g = 8 * g + 3`; ARITH_RULE `4 + 8 * g = 8 * g + 4`; ARITH_RULE `5 + 8 * g = 8 * g + 5`] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;;

let FOLD_Q19_REM6 : tactic =
  (* rem = 6 -> rem4_drain, entered at step 65: fold at s123 (65 + 58). *)
  fold_q19_at `read Q19 s123 : int128` `8 * g + 6` TAIL_Q19_FOLD_REM6;;

let AES_GCM_ENC_ALT_TAIL_REM6 = prove
 (kterm `!q27_init in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce c rk inblock nb g pc.
    nb = 8 * g + 6 /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (key_p, keybytes); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + pc_tail) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q27 s = q27_init /\
           read Q28 s = word_reversefields 8 (EL nr rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 8)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 2)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 3)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 4)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 5)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 6)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 7)) rk) /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (\s. read PC s = word (pc + pc_end) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; htable_mem_4; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES_GCM_ENC_ALT_EXEC]
    (kterm `LENGTH tmc`)]) THEN
  SUBGOAL_THEN
   `    read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 16)))) s0 =
    inblock (8 * g + 1) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 32)))) s0 =
    inblock (8 * g + 2) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 48)))) s0 =
    inblock (8 * g + 3) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 64)))) s0 =
    inblock (8 * g + 4) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 80)))) s0 =
    inblock (8 * g + 5)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g = 16 * (8 * g)`;
      ARITH_RULE `128 * g + 16 = 16 * (8 * g + 1)`;
      ARITH_RULE `128 * g + 32 = 16 * (8 * g + 2)`;
      ARITH_RULE `128 * g + 48 = 16 * (8 * g + 3)`;
      ARITH_RULE `128 * g + 64 = 16 * (8 * g + 4)`;
      ARITH_RULE `128 * g + 80 = 16 * (8 * g + 5)`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAIL_X5_REM6]) THEN
  MAP_EVERY NSTEP_GP (10--123) THEN
  FOLD_Q19_REM6 THEN
  DISCARD_DEAD_REDUCE_SCRATCH THEN
  MAP_EVERY NSTEP_GP (124--127) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word_sub (word (8 * g + c + 8):int32) (word 1)) (word 1) = word (8 * g + c + 6)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 6` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 6 <=>
                       j < 8 * g \/ j = 8 * g \/ j = 8 * g + 1 \/ j = 8 * g + 2 \/ j = 8 * g + 3 \/ j = 8 * g + 4 \/ j = 8 * g + 5`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rkn = word_xor ch (word_xor rkn inb)`] THEN
  REWRITE_TAC[XOR_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `8 * g + c = c + 8 * g`] THEN
  REWRITE_TAC[ADD_ASSOC] THEN
  REWRITE_TAC[ARITH_RULE `1 + c = c + 1`; ARITH_RULE `2 + c = c + 2`;
              ARITH_RULE `3 + c = c + 3`; ARITH_RULE `4 + c = c + 4`;
              ARITH_RULE `5 + c = c + 5`; ARITH_RULE `6 + c = c + 6`;
              ARITH_RULE `7 + c = c + 7`] THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* ========================================================================= *)
(* Tail cascade arm rem=7 (nblocks = 8*g+7), lands at 0xfc0.                 *)
(* 7-block batched Q19 fold; Q27 pinned (q27_init).  1 `sub v30` decrement   *)
(* rolls the counter 8g+c+8 -> 8g+c+7 = nb+c.                                *)
(* ========================================================================= *)

let TAIL_Q19_FOLD_REM7 =
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
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [ARITH_RULE `8 * g + c + 1 = (8 * g + 1) + c`;
     ARITH_RULE `8 * g + c + 2 = (8 * g + 2) + c`;
     ARITH_RULE `8 * g + c + 3 = (8 * g + 3) + c`;
     ARITH_RULE `8 * g + c + 4 = (8 * g + 4) + c`;
     ARITH_RULE `8 * g + c + 5 = (8 * g + 5) + c`;
     ARITH_RULE `8 * g + c + 6 = (8 * g + 6) + c`] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN
  REWRITE_TAC[GSYM cipher_block] THEN REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_XOR] THEN
  REWRITE_TAC[KARATSUBA_IS_DOT_HW] THEN
  REWRITE_TAC[KDOT_B0] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `8 * g + 7 = SUC(SUC(SUC(SUC(SUC(SUC(SUC(8 * g)))))))`;
              ARITH_RULE `7 + 8 * g = SUC(SUC(SUC(SUC(SUC(SUC(SUC(8 * g)))))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  MP_TAC(ISPECL
    [kterm `ghash_twist (cipher (word 0) rk)`;
     kterm `[nist_cipher_block cipher c nonce rk inblock (8*g+1);
       nist_cipher_block cipher c nonce rk inblock (8*g+2);
       nist_cipher_block cipher c nonce rk inblock (8*g+3);
       nist_cipher_block cipher c nonce rk inblock (8*g+4);
       nist_cipher_block cipher c nonce rk inblock (8*g+5);
       nist_cipher_block cipher c nonce rk inblock (8*g+6)]:(int128)list`;
     kterm `ghash_polyval_acc (ghash_twist (cipher (word 0) rk)) tag0
        (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8*g))`;
     kterm `nist_cipher_block cipher c nonce rk inblock (8*g)`]
    GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ADD_0] THEN
  REWRITE_TAC[polyval_dot] THEN
  REWRITE_TAC[GSYM PROP3_XOR] THEN
  REWRITE_TAC[NCB_ETA] THEN
  REWRITE_TAC[ARITH_RULE `1 + 8 * g = 8 * g + 1`; ARITH_RULE `2 + 8 * g = 8 * g + 2`; ARITH_RULE `3 + 8 * g = 8 * g + 3`; ARITH_RULE `4 + 8 * g = 8 * g + 4`; ARITH_RULE `5 + 8 * g = 8 * g + 5`; ARITH_RULE `6 + 8 * g = 8 * g + 6`] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;;

let FOLD_Q19_REM7 : tactic =
  (* rem = 7 -> rem4_drain, entered at step 71: fold at s129 (71 + 58). *)
  fold_q19_at `read Q19 s129 : int128` `8 * g + 7` TAIL_Q19_FOLD_REM7;;

let AES_GCM_ENC_ALT_TAIL_REM7 = prove
 (kterm `!q27_init in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce c rk inblock nb g pc.
    nb = 8 * g + 7 /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (key_p, keybytes); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + pc_tail) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q27 s = q27_init /\
           read Q28 s = word_reversefields 8 (EL nr rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 8)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 2)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 3)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 4)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 5)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 6)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c + 7)) rk) /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (\s. read PC s = word (pc + pc_end) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; htable_mem_4; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES_GCM_ENC_ALT_EXEC]
    (kterm `LENGTH tmc`)]) THEN
  SUBGOAL_THEN
   `    read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 16)))) s0 =
    inblock (8 * g + 1) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 32)))) s0 =
    inblock (8 * g + 2) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 48)))) s0 =
    inblock (8 * g + 3) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 64)))) s0 =
    inblock (8 * g + 4) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 80)))) s0 =
    inblock (8 * g + 5) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 96)))) s0 =
    inblock (8 * g + 6)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g = 16 * (8 * g)`;
      ARITH_RULE `128 * g + 16 = 16 * (8 * g + 1)`;
      ARITH_RULE `128 * g + 32 = 16 * (8 * g + 2)`;
      ARITH_RULE `128 * g + 48 = 16 * (8 * g + 3)`;
      ARITH_RULE `128 * g + 64 = 16 * (8 * g + 4)`;
      ARITH_RULE `128 * g + 80 = 16 * (8 * g + 5)`;
      ARITH_RULE `128 * g + 96 = 16 * (8 * g + 6)`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAIL_X5_REM7]) THEN
  MAP_EVERY NSTEP_GP (10--129) THEN
  FOLD_Q19_REM7 THEN
  DISCARD_DEAD_REDUCE_SCRATCH THEN
  MAP_EVERY NSTEP_GP (130--133) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word (8 * g + c + 8):int32) (word 1) = word (8 * g + c + 7)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 7` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 7 <=>
                       j < 8 * g \/ j = 8 * g \/ j = 8 * g + 1 \/ j = 8 * g + 2 \/ j = 8 * g + 3 \/ j = 8 * g + 4 \/ j = 8 * g + 5 \/ j = 8 * g + 6`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rkn = word_xor ch (word_xor rkn inb)`] THEN
  REWRITE_TAC[XOR_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `8 * g + c = c + 8 * g`] THEN
  REWRITE_TAC[ADD_ASSOC] THEN
  REWRITE_TAC[ARITH_RULE `1 + c = c + 1`; ARITH_RULE `2 + c = c + 2`;
              ARITH_RULE `3 + c = c + 3`; ARITH_RULE `4 + c = c + 4`;
              ARITH_RULE `5 + c = c + 5`; ARITH_RULE `6 + c = c + 6`;
              ARITH_RULE `7 + c = c + 7`] THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* ========================================================================= *)
(* Tail cascade arm rem=8 (nblocks = 8*g+8), lands at 0x1178                 *)
(* (L256_enc_exact8_drain), for every g >= 0.                                *)
(*                                                                           *)
(* TAIL_REM8 is stated for every group count g, including nblocks = 8 and    *)
(* 16, which the (nblocks-1) DIV 8 decomposition also routes here; its drive *)
(* does not depend on g (x5 = 128).  Its helpers are the x5 value            *)
(* TAIL_X5_128_G and the Q19 fold TAIL_Q19_FOLD_G.                           *)
(* ========================================================================= *)

(* TAIL_Q19_FOLD_G: the rem = 8 fold, advancing Q19 from nist_ghash..(8*g)   *)
(* to nist_ghash..(8*g+8).  It is not Q19_FOLD_TAC_K, because the tail's     *)
(* reduce differs from the prepretail's in two ways.                         *)
(* (1) The operand order of the final reduce eor3.  The prepretail's         *)
(*     `eor3 v19,v19,v21,v17` (0xec0) is `word_xor (word_xor p3 ext) pmull`  *)
(*     and needs a leading AC-swap to reach ghash_reduce_raw's `word_xor     *)
(*     (word_xor p3 pmull) ext` shape; the tail's `eor3 v19,v19,v17,v21`     *)
(*     (0x1314) is already in ghash_reduce_raw order, so no AC-swap          *)
(*     is applied.                                                           *)
(* (2) The block provenance.  The prepretail folds the invariant-clean       *)
(*     v8..v15 blocks (`word_xor (aes_ctr_block J) (inblock J)`); the tail   *)
(*     computes its blocks fresh (eor3 v9,..,vN,v29 + KS_SOLVE), so each     *)
(*     block enters the reduce in the raw form `word_xor (word_xor inblock   *)
(*     (word_xor aes rkn)) rkn` (double rkn, inblock first, aes not          *)
(*     folded to aes_ctr_block).  The fold first normalises it: a            *)
(*     WORD_BITWISE_RULE rewrite cancels the double rkn, RECON_GRR exposes   *)
(*     ghash_reduce_raw, WORD_REDUCE_CONV + WORD_XOR_0 clear a spurious      *)
(*     word_subword (word 0) (64,64), a second rewrite puts the AES term     *)
(*     first, and the counter reindexing 8*g+c+j = (8*g+j)+c lets GSYM       *)
(*     aes_ctr_block fold rev8 (cipher (ctr_block nonce (J+c)) rk) to        *)
(*     aes_ctr_block J, after which GSYM cipher_block + CIPHER_BLOCK_NIST    *)
(*     reach nist_cipher_block.                                              *)
(* After this cleaning the tail's three Karatsuba lanes are aligned (the     *)
(* same block order on all lanes), so GHASH_REDUCE_RAW_XOR (linearity in any *)
(* order) + KARATSUBA_IS_DOT_HW give 8 clean polyval_dots directly, without  *)
(* DIST8_PLAIN (which assumes the body's [1;0;3;2..] cross order); the       *)
(* batched fold then closes as in the main loop, with NCB_ETA for the        *)
(* block-0 lambda.                                                           *)
let TAIL_Q19_FOLD_G =
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
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [ARITH_RULE `8 * g + c + 1 = (8 * g + 1) + c`;
     ARITH_RULE `8 * g + c + 2 = (8 * g + 2) + c`;
     ARITH_RULE `8 * g + c + 3 = (8 * g + 3) + c`;
     ARITH_RULE `8 * g + c + 4 = (8 * g + 4) + c`;
     ARITH_RULE `8 * g + c + 5 = (8 * g + 5) + c`;
     ARITH_RULE `8 * g + c + 6 = (8 * g + 6) + c`;
     ARITH_RULE `8 * g + c + 7 = (8 * g + 7) + c`] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN
  REWRITE_TAC[GSYM cipher_block] THEN REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_XOR] THEN
  REWRITE_TAC[KARATSUBA_IS_DOT_HW] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE
    `8 * g + 8 = SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(8 * g))))))))`;
              ARITH_RULE `8 + 8 * g = SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(8 * g))))))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  MP_TAC(ISPECL
    [kterm `ghash_twist (cipher (word 0) rk)`;
     kterm `[nist_cipher_block cipher c nonce rk inblock (8 * g+1);
       nist_cipher_block cipher c nonce rk inblock (8 * g+2);
       nist_cipher_block cipher c nonce rk inblock (8 * g+3);
       nist_cipher_block cipher c nonce rk inblock (8 * g+4);
       nist_cipher_block cipher c nonce rk inblock (8 * g+5);
       nist_cipher_block cipher c nonce rk inblock (8 * g+6);
       nist_cipher_block cipher c nonce rk inblock (8 * g+7)]:(int128)list`;
     kterm `ghash_polyval_acc (ghash_twist (cipher (word 0) rk)) tag0
        (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8 * g))`;
     kterm `nist_cipher_block cipher c nonce rk inblock (8 * g)`]
    GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ADD_0] THEN
  REWRITE_TAC[polyval_dot] THEN
  REWRITE_TAC[GSYM PROP3_XOR] THEN
  REWRITE_TAC[NCB_ETA] THEN
  REWRITE_TAC[ARITH_RULE `1 + 8 * g = 8 * g + 1`; ARITH_RULE `2 + 8 * g = 8 * g + 2`; ARITH_RULE `3 + 8 * g = 8 * g + 3`; ARITH_RULE `4 + 8 * g = 8 * g + 4`; ARITH_RULE `5 + 8 * g = 8 * g + 5`; ARITH_RULE `6 + 8 * g = 8 * g + 6`; ARITH_RULE `7 + 8 * g = 8 * g + 7`] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;;

let FOLD_Q19_S114_G : tactic =
  fold_q19_at `read Q19 s115 : int128` `8 * g + 8` TAIL_Q19_FOLD_G;;

let AES_GCM_ENC_ALT_TAIL_REM8 = prove
 (kterm `!q18_init q27_init in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce c rk inblock nb g pc.
    8 * g + 8 = nb /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (key_p, keybytes); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + pc_tail) /\
           read Q18 s = q18_init /\
           read Q27 s = q27_init /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           wordlist_from_memory(key_p,nrk) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q28 s = word_reversefields 8 (EL nr rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 8)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block cipher c nonce rk inblock)
                              (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * g + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * g + c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * g + c + 2)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * g + c + 3)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * g + c + 4)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * g + c + 5)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * g + c + 6)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * g + c + 7)) rk) /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (\s. read PC s = word (pc + pc_end) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[KEY_SPLIT] THEN
  REWRITE_TAC[htable_mem_8; htable_mem_4; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES_GCM_ENC_ALT_EXEC]
    (kterm `LENGTH tmc`)]) THEN
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 16)))) s0 =
    inblock (8 * g + 1) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 32)))) s0 =
    inblock (8 * g + 2) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 48)))) s0 =
    inblock (8 * g + 3) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 64)))) s0 =
    inblock (8 * g + 4) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 80)))) s0 =
    inblock (8 * g + 5) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 96)))) s0 =
    inblock (8 * g + 6) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 112)))) s0 =
    inblock (8 * g + 7)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE
     `128 * g + 16 = 16 * (8 * g + 1) /\
      128 * g + 32 = 16 * (8 * g + 2) /\
      128 * g + 48 = 16 * (8 * g + 3) /\
      128 * g + 64 = 16 * (8 * g + 4) /\
      128 * g + 80 = 16 * (8 * g + 5) /\
      128 * g + 96 = 16 * (8 * g + 6) /\
      128 * g + 112 = 16 * (8 * g + 7)`] THEN
    REWRITE_TAC[ARITH_RULE `128 * a = 16 * 8 * a`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP TAIL_X5_128_G (ASSUME `8 * g + 8 = nb`)]) THEN
  DISCARD_DEAD_KEYMEM THEN
  DISCARD_DEAD_HTABLE THEN
  DISCARD_REGS ["Q31"; "Q28"] THEN
  (* Q27 is last read at step 94 (eor3 v18,v18,v27,v15 at 0x12c0), so it is  *)
  (* dropped after s97; the final reduce eor3 at 0x1314 is step 115, where   *)
  (* Q19 is folded; the writebacks are the str q30 at step 98 and the st1 at *)
  (* step 118.                                                               *)
  MAP_EVERY NSTEP_GP (10--97) THEN
  DISCARD_REGS ["Q27"] THEN
  MAP_EVERY NSTEP_GP (98--115) THEN
  (* Rewrite nb back to 8*g+8 in the Q19 fact only (the hypothesis           *)
  (* 8*g+8 = nb is still needed by the tag and out-block closers), so that   *)
  (* the fold sees all 8 block indices in the 8*g+j form.                    *)
  RULE_ASSUM_TAC(fun th ->
    if (try lhs(concl th) = `read Q19 s115:int128` with Failure _ -> false)
    then REWRITE_RULE[SYM(ASSUME `8 * g + 8 = nb`)] th else th) THEN
  FOLD_Q19_S114_G THEN
  DISCARD_DEAD_REDUCE_SCRATCH THEN
  MAP_EVERY NSTEP_GP (116--119) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [
    REWRITE_TAC[IVEC_STORE_REV32] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `8 * g + 8 = nb` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [
    FIRST_X_ASSUM(fun th ->
      if concl th = `8 * g + 8 = nb` then SUBST_ALL_TAC(SYM th) else failwith "") THEN
    REWRITE_TAC[TAG_STORE_REV64] THEN AP_TERM_TAC THEN TAIL_Q19_FOLD_G;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if concl th = `8 * g + 8 = nb` then SUBST_ALL_TAC(SYM th) else failwith "") THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 8 <=>
                       j < 8 * g \/ j = 8 * g \/ j = 8 * g + 1 \/
                       j = 8 * g + 2 \/ j = 8 * g + 3 \/ j = 8 * g + 4 \/
                       j = 8 * g + 5 \/ j = 8 * g + 6 \/ j = 8 * g + 7`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8; CTR_BLOCK_RECONSTRUCT_REV32] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rkn = word_xor ch (word_xor rkn inb)`] THEN
  REWRITE_TAC[XOR_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
  REWRITE_TAC[ADD_ASSOC; ARITH] THEN
  (* close the ciphertext identity at the aes_ctr_block level (TAIL pattern):
     a plain GSYM cipher_block fold is higher-order ambiguous under c. *)
  REWRITE_TAC[CIPHER_KEYLIST] THEN
  REWRITE_TAC[aes_ctr_block; ADD_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `8 * g + c = c + 8 * g`] THEN
  REWRITE_TAC[ADD_ASSOC] THEN
  REWRITE_TAC[ARITH_RULE `(c + 8 * g) + 1 = (1 + 8 * g) + c`;
              ARITH_RULE `(c + 8 * g) + 2 = (2 + 8 * g) + c`;
              ARITH_RULE `(c + 8 * g) + 3 = (3 + 8 * g) + c`;
              ARITH_RULE `(c + 8 * g) + 4 = (4 + 8 * g) + c`;
              ARITH_RULE `(c + 8 * g) + 5 = (5 + 8 * g) + c`;
              ARITH_RULE `(c + 8 * g) + 6 = (6 + 8 * g) + c`;
              ARITH_RULE `(c + 8 * g) + 7 = (7 + 8 * g) + c`] THEN
  REPEAT CONJ_TAC THEN
  TRY(CONV_TAC WORD_RULE) THEN
  TRY(CONV_TAC WORD_BITWISE_RULE) THEN
  REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
  TRY ARITH_TAC);;

(* The cases r = 2..7 of AES_GCM_ENC_ALT_TAIL_REM below: weaken the unified  *)
(* precondition to the one these arms share (no Q18 pin and no round-key     *)
(* reads) and apply the arm th.                                              *)
let TAIL_REM_ARM_TAC th =
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
  EXISTS_TAC
   (kterm `(\s. aligned_bytes_loaded s (word pc) tmc /\
        read PC s = word (pc + pc_tail) /\
        read X0 s = word_add in_p (word (128 * g)) /\
        read X2 s = word_add out_p (word (128 * g)) /\
        read X3 s = tag_p /\
        read X9 s = word (16 * nb) /\
        read X4 s = word_add in_p (word (16 * nb)) /\
        read X16 s = ivec_p /\
        read X5 s = end_p /\
        read X6 s = htable_p /\
        read X10 s = mod_p /\
        read X11 s = key_p /\
        read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
        read (memory :> bytes128 ivec_p) s =
          word_reversefields 8 (ctr_block nonce c) /\
        read Q27 s = q27_init /\
        read Q28 s = word_reversefields 8 (EL nr rk) /\
        read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 8)) /\
        read Q31 s = word 79228162514264337593543950336 /\
        read Q19 s =
          nist_ghash (cipher (word 0) rk) tag0
              (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8 * g)) /\
        word_xor (read Q0 s) (word_reversefields 8 (EL nr rk)) =
          word_reversefields 8
            (cipher (ctr_block nonce (8 * g + c)) rk) /\
        word_xor (read Q1 s) (word_reversefields 8 (EL nr rk)) =
          word_reversefields 8
            (cipher (ctr_block nonce (8 * g + c + 1)) rk) /\
        word_xor (read Q2 s) (word_reversefields 8 (EL nr rk)) =
          word_reversefields 8
            (cipher (ctr_block nonce (8 * g + c + 2)) rk) /\
        word_xor (read Q3 s) (word_reversefields 8 (EL nr rk)) =
          word_reversefields 8
            (cipher (ctr_block nonce (8 * g + c + 3)) rk) /\
        word_xor (read Q4 s) (word_reversefields 8 (EL nr rk)) =
          word_reversefields 8
            (cipher (ctr_block nonce (8 * g + c + 4)) rk) /\
        word_xor (read Q5 s) (word_reversefields 8 (EL nr rk)) =
          word_reversefields 8
            (cipher (ctr_block nonce (8 * g + c + 5)) rk) /\
        word_xor (read Q6 s) (word_reversefields 8 (EL nr rk)) =
          word_reversefields 8
            (cipher (ctr_block nonce (8 * g + c + 6)) rk) /\
        word_xor (read Q7 s) (word_reversefields 8 (EL nr rk)) =
          word_reversefields 8
            (cipher (ctr_block nonce (8 * g + c + 7)) rk) /\
        htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
        (!j. j < nb
             ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                 inblock j) /\
        (!j. j < 8 * g
             ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                 word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))`) THEN
  CONJ_TAC THENL
   [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC th THEN
    REPEAT CONJ_TAC THEN (ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[])];;

(* ========================================================================= *)
(* TAIL_REM (rem in 1..8, g >= 0).                                           *)
(*                                                                           *)
(* One theorem for the whole cascade at entry pc+0xee0, for any leftover     *)
(* block count r in 1..8 and any group count g >= 0.  The proof splits on r; *)
(* each case weakens the unified (strongest) precondition to that arm's      *)
(* precondition with ENSURES_PRECONDITION_THM (the arms REM1..REM7 need      *)
(* fewer register pins and keystreams; REM8 needs all) and then applies the  *)
(* matching TAIL_REM<r>.  The unified precondition pins q18_init/q27_init,   *)
(* all 8 keystreams and the nrk round-key memory facts (REM8's               *)
(* precondition); the weakening drops whatever each smaller arm omits.       *)
(* BETA_TAC before STRIP_TAC is needed: the precondition is a lambda redex,  *)
(* and STRIP_TAC first would keep it unreduced.                              *)
(* ========================================================================= *)

let AES_GCM_ENC_ALT_TAIL_REM = prove
 (kterm `!q18_init q27_init in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce c rk inblock nb r g pc.
    nb = 8 * g + r /\
    1 <= r /\ r <= 8 /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (key_p, keybytes); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + pc_tail) /\
           read Q18 s = q18_init /\
           read Q27 s = q27_init /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           wordlist_from_memory(key_p,nrk) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q28 s = word_reversefields 8 (EL nr rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 8)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block cipher c nonce rk inblock)
                              (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * g + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * g + c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * g + c + 2)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * g + c + 3)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * g + c + 4)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * g + c + 5)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * g + c + 6)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * g + c + 7)) rk) /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (\s. read PC s = word (pc + pc_end) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `r=1\/r=2\/r=3\/r=4\/r=5\/r=6\/r=7\/r=8` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THENL
   [    (MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC (kterm `(\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + pc_tail) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q28 s = word_reversefields 8 (EL nr rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 8)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8
               (cipher (ctr_block nonce (8 * g + c)) rk) /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))`) THEN
     CONJ_TAC THENL
      [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC AES_GCM_ENC_ALT_TAIL_REM1 THEN
       REPEAT CONJ_TAC THEN (ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[])]);
    TAIL_REM_ARM_TAC AES_GCM_ENC_ALT_TAIL_REM2;
    TAIL_REM_ARM_TAC AES_GCM_ENC_ALT_TAIL_REM3;
    TAIL_REM_ARM_TAC AES_GCM_ENC_ALT_TAIL_REM4;
    TAIL_REM_ARM_TAC AES_GCM_ENC_ALT_TAIL_REM5;
    TAIL_REM_ARM_TAC AES_GCM_ENC_ALT_TAIL_REM6;
    TAIL_REM_ARM_TAC AES_GCM_ENC_ALT_TAIL_REM7;
    (MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC (kterm `(\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + pc_tail) /\
           read Q18 s = q18_init /\
           read Q27 s = q27_init /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           wordlist_from_memory(key_p,nrk) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q28 s = word_reversefields 8 (EL nr rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 8)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block cipher c nonce rk inblock)
                              (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * g + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * g + c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * g + c + 2)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * g + c + 3)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * g + c + 4)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * g + c + 5)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * g + c + 6)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * g + c + 7)) rk) /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))`) THEN
     CONJ_TAC THENL
      [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC AES_GCM_ENC_ALT_TAIL_REM8 THEN
       REPEAT CONJ_TAC THEN (ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[])])]);;

(* ========================================================================= *)
(* Full-body assembly: core entry pc+0x38 (SETUP) -> exit pc+0x1154 (TAIL).  *)
(*                                                                           *)
(* GEN_CORRECT (nb >= 17) nests three ENSURES_SEQUENCE_TACs, at 0x4c0, 0xa10 *)
(* and 0xee0.  The first leg of each frame-subsumes the segment's MAYCHANGE  *)
(* into the whole frame (ENSURES_FRAME_SUBSUMED + SUBSUMED_MAYCHANGE_TAC)    *)
(* and then applies the segment theorem by MP_TAC ... DISCH_THEN             *)
(* MATCH_MP_TAC (as in AES_XTS_ENCRYPT_LT_2BLOCK_CORRECT).  The PREPRETAIL   *)
(* -> TAIL join uses an existential Q18/Q27 mid-state: the mid predicate is  *)
(* `?v18 v27. read Q18 s = v18 /\ read Q27 s = v27 /\ <PREPRETAIL post       *)
(* without the tag memory>`; the PREPRETAIL leg proves it by EXISTS_TAC      *)
(* (read Q18 s) / (read Q27 s), and the TAIL leg strips the existential and  *)
(* applies AES_GCM_ENC_ALT_TAIL_REM (g = k+1, r = nb - 8*(k+1)) to           *)
(* the witnesses.                                                            *)
(* ========================================================================= *)

(* Frame note: the SETUP/MAIN_LOOP/PREPRETAIL frames are subsets of the      *)
(* CORRECT frame (ABI ,, Q8..Q15 ,, mem[out_p;tag_p;ivec_p]).  SETUP writes  *)
(* only out_p memory (and registers); PREPRETAIL writes no memory (its frame *)
(* still lists out_p); the TAIL writes out_p, tag_p and ivec_p.              *)

let LENGTH_WB_MC =
  (REWRITE_CONV [fst AES_GCM_ENC_ALT_EXEC]) (kterm `LENGTH tmc`);;

let AES_GCM_ENC_ALT_GEN_CORRECT = prove
 (kterm `!in_p out_p tag_p ivec_p key_p htable_p stackpointer len_bits end_p
     tag0 nonce c rk inblock nb k pc.
    ~(k = 0) /\
    8 * (k + 1) <= nb /\
    len_bits = 128 * nb /\
    8 * (k + 1) < nb /\ nb <= 8 * (k + 2) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (key_p, keybytes); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word len_bits /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (len_bits DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           wordlist_from_memory(key_p,nrk) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. read PC s = word (pc + pc_end) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  (* ENSURES_SEQUENCE_TAC adds the `aligned_bytes_loaded` (program_decodes)  *)
  (* and `read PC s = word pc'` conjuncts to both legs' mid-state, so the    *)
  (* mid-state argument omits them (only the register/memory remainder is    *)
  (* given).  It also runs MAYCHANGE_IDEMPOT_TAC internally, which fails if  *)
  (* the ABI macro is folded, so the macro is unfolded first.                *)
  (*                                                                         *)
  (* Expand the core precondition's ALLPAIRS + PAIRWISE into individual      *)
  (* nonoverlapping atoms before stripping, so that each segment leg's       *)
  (* antecedents are available as assumptions for ASM_SIMP/ASM_REWRITE       *)
  (* (SETUP's precondition needs out_p vs tag_p and ivec_p, which are        *)
  (* PAIRWISE facts of CORRECT, not ALLPAIRS ones).                          *)
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN

  (* ============ SEQUENCE 1: SETUP  pc+0x38 -> pc+0x4c0 ============        *)
  (* mid-state: no aligned_bytes_loaded or read PC (the tactic adds them).   *)
  ENSURES_SEQUENCE_TAC (kterm `pc + pc_loop`)
   (kterm `\s. read X0 s = word_add in_p (word (128 * (0 + 1))) /\
        read X2 s = word_add out_p (word (128 * (0 + 1))) /\
        read X3 s = tag_p /\
        read X9 s = word (16 * nb) /\
        read X4 s = word_add in_p (word (16 * nb)) /\
        read X16 s = ivec_p /\
        read X5 s = end_p /\
        read X6 s = htable_p /\
        read X10 s = word_add stackpointer (word 0x40) /\
        read X11 s = key_p /\
        read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
          word 0xc200000000000000 /\
        wordlist_from_memory(key_p,nrk) s = MAP (word_reversefields 8) rk /\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
        read (memory :> bytes128 ivec_p) s =
          word_reversefields 8 (ctr_block nonce c) /\
        read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + c + 13)) /\
        read Q31 s = word 79228162514264337593543950336 /\
        read Q19 s =
          nist_ghash (cipher (word 0) rk) tag0
              (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8 * 0)) /\
        read Q8 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 0))) (inblock (8 * 0 + 0)) /\
        read Q9 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 1))) (inblock (8 * 0 + 1)) /\
        read Q10 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 2))) (inblock (8 * 0 + 2)) /\
        read Q11 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 3))) (inblock (8 * 0 + 3)) /\
        read Q12 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 4))) (inblock (8 * 0 + 4)) /\
        read Q13 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 5))) (inblock (8 * 0 + 5)) /\
        read Q14 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 6))) (inblock (8 * 0 + 6)) /\
        read Q15 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 7))) (inblock (8 * 0 + 7)) /\
        read Q0 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 8)) /\
        read Q1 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 9)) /\
        read Q2 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 10)) /\
        read Q3 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 11)) /\
        read Q4 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 12)) /\
        htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
        (!j. j < nb
             ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                 inblock j) /\
        (!j. j < 8 * (0 + 1)
             ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                 word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)) /\
        ((read NF s <=> read VF s) <=> (0 = k))`) THEN
  CONJ_TAC THENL
   [(* SETUP leg *)
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
      MAYCHANGE [memory :> bytes(out_p, 16 * nb)]` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
              MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
      SUBSUMED_MAYCHANGE_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
      `key_p:int64`; `htable_p:int64`; `stackpointer:int64`; `len_bits:num`;
      `end_p:int64`; `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`;
      `inblock:num->int128`; `nb:num`; `k:num`; `pc:num`]
     AES_GCM_ENC_ALT_SETUP_GEN) THEN
    REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[NONOVERLAPPING_CLAUSES] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN

  (* ============ SEQUENCE 2: MAIN_LOOP  pc+0x4c0 -> pc+0xa10 ============   *)
  (* mid-state = the PREPRETAIL_GEN precondition (pc+0xa10) without aligned  *)
  (* and PC, with mod_p := stackpointer+0x40, written out explicitly.        *)
  ENSURES_SEQUENCE_TAC (kterm `pc + pc_prepretail`)
   (kterm `\s. read X0 s = word_add in_p (word (128 * (k + 1))) /\
        read X2 s = word_add out_p (word (128 * (k + 1))) /\
        read X3 s = tag_p /\
        read X9 s = word (16 * nb) /\
        read X4 s = word_add in_p (word (16 * nb)) /\
        read X16 s = ivec_p /\
        read X5 s = end_p /\
        read X6 s = htable_p /\
        read X10 s = word_add stackpointer (word 0x40) /\
        read X11 s = key_p /\
        read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
          word 0xc200000000000000 /\
        wordlist_from_memory(key_p,nrk) s = MAP (word_reversefields 8) rk /\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
        read (memory :> bytes128 ivec_p) s =
          word_reversefields 8 (ctr_block nonce c) /\
        read Q30 s = word_reversefields 32 (ctr_block nonce (8 * k + c + 13)) /\
        read Q31 s = word 79228162514264337593543950336 /\
        read Q19 s =
          nist_ghash (cipher (word 0) rk) tag0
              (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8 * k)) /\
        read Q8 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * k + 0))) (inblock (8 * k + 0)) /\
        read Q9 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * k + 1))) (inblock (8 * k + 1)) /\
        read Q10 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * k + 2))) (inblock (8 * k + 2)) /\
        read Q11 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * k + 3))) (inblock (8 * k + 3)) /\
        read Q12 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * k + 4))) (inblock (8 * k + 4)) /\
        read Q13 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * k + 5))) (inblock (8 * k + 5)) /\
        read Q14 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * k + 6))) (inblock (8 * k + 6)) /\
        read Q15 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * k + 7))) (inblock (8 * k + 7)) /\
        read Q0 s = word_reversefields 8 (ctr_block nonce (8 * k + c + 8)) /\
        read Q1 s = word_reversefields 8 (ctr_block nonce (8 * k + c + 9)) /\
        read Q2 s = word_reversefields 8 (ctr_block nonce (8 * k + c + 10)) /\
        read Q3 s = word_reversefields 8 (ctr_block nonce (8 * k + c + 11)) /\
        read Q4 s = word_reversefields 8 (ctr_block nonce (8 * k + c + 12)) /\
        htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
        (!j. j < nb
             ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                 inblock j) /\
        (!j. j < 8 * (k + 1)
             ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                 word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j))`) THEN
  CONJ_TAC THENL
   [(* MAIN_LOOP leg *)
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
      MAYCHANGE [memory :> bytes(out_p, 16 * nb)]` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
              MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
      SUBSUMED_MAYCHANGE_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
      `key_p:int64`; `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
      `end_p:int64`; `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`;
      `inblock:num->int128`; `nb:num`; `k:num`; `pc:num`]
     AES_GCM_ENC_ALT_MAIN_LOOP) THEN
    REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[NONOVERLAPPING_CLAUSES] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN

  (* ============ SEQUENCE 3: PREPRETAIL  pc+0xa10 -> pc+0xee0 ============  *)
  (* mid-state = ?v18 v27. read Q18 s = v18 /\ read Q27 s = v27 /\ <the      *)
  (* PREPRETAIL_GEN postcondition, with mod_p -> stackpointer+0x40, without  *)
  (* the tag memory, aligned and PC>.  ENSURES_SEQUENCE_TAC adds             *)
  (* aligned_bytes_loaded and read PC outside the existential, so on the     *)
  (* TAIL leg the precondition is `\s. aligned .. /\ read PC s = .. /\ (?v18 *)
  (* v27. ...)`; the TAIL leg hoists the existential with GSYM               *)
  (* RIGHT_EXISTS_AND_THM / LEFT_EXISTS_AND_THM before                       *)
  (* ENSURES_EXISTS2_PRECONDITION.                                           *)
  ENSURES_SEQUENCE_TAC (kterm `pc + pc_tail`)
   (kterm `\s. ?v18 v27.
        read Q18 s = v18 /\ read Q27 s = v27 /\
        read X0 s = word_add in_p (word (128 * (k + 1))) /\
        read X2 s = word_add out_p (word (128 * (k + 1))) /\
        read X3 s = tag_p /\
        read X9 s = word (16 * nb) /\
        read X4 s = word_add in_p (word (16 * nb)) /\
        read X16 s = ivec_p /\
        read X5 s = end_p /\
        read X6 s = htable_p /\
        read X10 s = word_add stackpointer (word 0x40) /\
        read X11 s = key_p /\
        read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
          word 0xc200000000000000 /\
        wordlist_from_memory(key_p,nrk) s = MAP (word_reversefields 8) rk /\
        read (memory :> bytes128 ivec_p) s =
          word_reversefields 8 (ctr_block nonce c) /\
        read Q28 s = word_reversefields 8 (EL nr rk) /\
        read Q30 s = word_reversefields 32 (ctr_block nonce (8 * k + c + 16)) /\
        read Q31 s = word 79228162514264337593543950336 /\
        read Q19 s =
          nist_ghash (cipher (word 0) rk) tag0
              (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8 * (k + 1))) /\
        word_xor (read Q0 s) (word_reversefields 8 (EL nr rk)) =
          word_reversefields 8 (cipher (ctr_block nonce (8 * k + c + 8)) rk) /\
        word_xor (read Q1 s) (word_reversefields 8 (EL nr rk)) =
          word_reversefields 8 (cipher (ctr_block nonce (8 * k + c + 9)) rk) /\
        word_xor (read Q2 s) (word_reversefields 8 (EL nr rk)) =
          word_reversefields 8 (cipher (ctr_block nonce (8 * k + c + 10)) rk) /\
        word_xor (read Q3 s) (word_reversefields 8 (EL nr rk)) =
          word_reversefields 8 (cipher (ctr_block nonce (8 * k + c + 11)) rk) /\
        word_xor (read Q4 s) (word_reversefields 8 (EL nr rk)) =
          word_reversefields 8 (cipher (ctr_block nonce (8 * k + c + 12)) rk) /\
        word_xor (read Q5 s) (word_reversefields 8 (EL nr rk)) =
          word_reversefields 8 (cipher (ctr_block nonce (8 * k + c + 13)) rk) /\
        word_xor (read Q6 s) (word_reversefields 8 (EL nr rk)) =
          word_reversefields 8 (cipher (ctr_block nonce (8 * k + c + 14)) rk) /\
        word_xor (read Q7 s) (word_reversefields 8 (EL nr rk)) =
          word_reversefields 8 (cipher (ctr_block nonce (8 * k + c + 15)) rk) /\
        htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
        (!j. j < nb
             ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                 inblock j) /\
        (!j. j < 8 * (k + 1)
             ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                 word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j))`) THEN
  CONJ_TAC THENL
   [(* PREPRETAIL leg: apply PREPRETAIL_GEN, then weaken its post to the     *)
    (* existential mid-state (the witnesses are the actual Q18/Q27 reads).   *)
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
      MAYCHANGE [memory :> bytes(out_p, 16 * nb)]` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
              MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
      SUBSUMED_MAYCHANGE_TAC;
      ALL_TAC] THEN
    (* Weaken the goal's post from Q_mid (the existential) to PREPRETAIL's   *)
    (* actual post with ENSURES_POSTCONDITION_TAC (MATCH_MP_TAC              *)
    (* ENSURES_POSTCONDITION_THM + EXISTS_TAC of the given post).  This      *)
    (* leaves two subgoals: (1) the pointwise implication PP_post ==> Q_mid  *)
    (* (closed by EXISTS_TAC (read Q18/Q27 s) + ASM_REWRITE), and (2)        *)
    (* `ensures arm PP_pre PP_post frame`, which is PREPRETAIL_GEN applied.  *)
    (* The post passed is PREPRETAIL_GEN's full postcondition, including     *)
    (* aligned_bytes_loaded and read PC.                                     *)
    ENSURES_POSTCONDITION_TAC
     (kterm `\s. aligned_bytes_loaded s (word pc) tmc /\
          read PC s = word (pc + pc_tail) /\
          read X0 s = word_add in_p (word (128 * (k + 1))) /\
          read X2 s = word_add out_p (word (128 * (k + 1))) /\
          read X3 s = tag_p /\ read X9 s = word (16 * nb) /\ read X4 s = word_add in_p (word (16 * nb)) /\
          read X16 s = ivec_p /\ read X5 s = end_p /\ read X6 s = htable_p /\
          read X10 s = word_add stackpointer (word 0x40) /\ read X11 s = key_p /\
          read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
            word 0xc200000000000000 /\
          wordlist_from_memory(key_p,nrk) s = MAP (word_reversefields 8) rk /\
          read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
          read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce c) /\
          read Q28 s = word_reversefields 8 (EL nr rk) /\
          read Q30 s = word_reversefields 32 (ctr_block nonce (8 * k + c + 16)) /\
          read Q31 s = word 79228162514264337593543950336 /\
          read Q19 s = nist_ghash (cipher (word 0) rk) tag0
              (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8 * (k + 1))) /\
          word_xor (read Q0 s) (word_reversefields 8 (EL nr rk)) =
            word_reversefields 8 (cipher (ctr_block nonce (8 * k + c + 8)) rk) /\
          word_xor (read Q1 s) (word_reversefields 8 (EL nr rk)) =
            word_reversefields 8 (cipher (ctr_block nonce (8 * k + c + 9)) rk) /\
          word_xor (read Q2 s) (word_reversefields 8 (EL nr rk)) =
            word_reversefields 8 (cipher (ctr_block nonce (8 * k + c + 10)) rk) /\
          word_xor (read Q3 s) (word_reversefields 8 (EL nr rk)) =
            word_reversefields 8 (cipher (ctr_block nonce (8 * k + c + 11)) rk) /\
          word_xor (read Q4 s) (word_reversefields 8 (EL nr rk)) =
            word_reversefields 8 (cipher (ctr_block nonce (8 * k + c + 12)) rk) /\
          word_xor (read Q5 s) (word_reversefields 8 (EL nr rk)) =
            word_reversefields 8 (cipher (ctr_block nonce (8 * k + c + 13)) rk) /\
          word_xor (read Q6 s) (word_reversefields 8 (EL nr rk)) =
            word_reversefields 8 (cipher (ctr_block nonce (8 * k + c + 14)) rk) /\
          word_xor (read Q7 s) (word_reversefields 8 (EL nr rk)) =
            word_reversefields 8 (cipher (ctr_block nonce (8 * k + c + 15)) rk) /\
          htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
          (!j. j < nb ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s = inblock j) /\
          (!j. j < 8 * (k + 1) ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                 word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j))`) THEN
    CONJ_TAC THENL
     [(* (1) PP_post ==> Q_mid.  PREPRETAIL_GEN's post includes              *)
      (* aligned_bytes_loaded, so the antecedent lambda given to             *)
      (* ENSURES_POSTCONDITION_TAC above does too.  X_GEN_TAC forces the     *)
      (* state variable to `s` (so that the pin witnesses match); BETA_TAC   *)
      (* reduces both the antecedent redex `(\s.OLD) s` and the consequent   *)
      (* redex `(\s.MID) s` before STRIP_TAC: if STRIP_TAC ran first it      *)
      (* would keep the antecedent as one unreduced redex and aligned would  *)
      (* never reach the assumptions.  Then REPEAT(CONJ_TAC ...) peels the   *)
      (* aligned and PC conjuncts (now assumptions) off the mid-state's      *)
      (* conjunction, and the actual Q18/Q27 reads witness the               *)
      (* remaining existential.                                              *)
      X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN
      REPEAT(CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      EXISTS_TAC `read Q18 s:int128` THEN EXISTS_TAC `read Q27 s:int128` THEN
      ASM_REWRITE_TAC[];
      (* (2) ensures PP_pre PP_post frame: PREPRETAIL_GEN applied. *)
      MP_TAC(ISPECL
       [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
        `key_p:int64`; `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
        `end_p:int64`; `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`;
        `inblock:num->int128`; `nb:num`; `k:num`; `pc:num`]
       AES_GCM_ENC_ALT_PREPRETAIL_GEN) THEN
      REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[NONOVERLAPPING_CLAUSES] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN

  (* ============ TAIL leg: pc+0xee0 -> pc+0x1154 ============               *)
  (* ENSURES_SEQUENCE_TAC wrapped the precondition as `\s.                   *)
  (* aligned_bytes_loaded .. /\ read PC s = word (pc+0xee0) /\ (?v18 v27.    *)
  (* ...)`, so the existential is not outermost.  GSYM RIGHT_EXISTS_AND_THM  *)
  (* / LEFT_EXISTS_AND_THM (`P /\ (?x. Q x)` -> `?x. P /\ Q x`), applied     *)
  (* under the \s. binder, hoist it to `\s. ?v18 v27. aligned .. /\ read PC  *)
  (* .. /\ read Q18 s = v18 /\ read Q27 s = v27 /\ B`, which matches         *)
  (* ENSURES_EXISTS2_PRECONDITION's `\s. ?v w. P v w s`.  MATCH_MP_TAC with  *)
  (* it turns the goal into `!v18 v27. ensures step (\s. ...) post frame`,   *)
  (* and AES_GCM_ENC_ALT_TAIL_REM is applied (ISPECL'd) to v18/v27.          *)
  REWRITE_TAC[GSYM RIGHT_EXISTS_AND_THM; GSYM LEFT_EXISTS_AND_THM] THEN
  MATCH_MP_TAC ENSURES_EXISTS2_PRECONDITION THEN
  MAP_EVERY X_GEN_TAC [`v18:int128`; `v27:int128`] THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC
   `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
    MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
    MAYCHANGE [memory :> bytes(out_p, 16 * nb);
               memory :> bytes(tag_p, 16);
               memory :> bytes(ivec_p, 16)]` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
            MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
    SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`v18:int128`; `v27:int128`;
    `in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
    `key_p:int64`; `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
    `end_p:int64`; `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`;
    `inblock:num->int128`; `nb:num`; `nb - 8 * (k + 1)`; `k + 1`; `pc:num`]
   AES_GCM_ENC_ALT_TAIL_REM) THEN
  REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  (* align TAIL_REM's ISPECL'd (g:=k+1) counters 8*(k+1)+c+M with the
     intermediate state's 8*k+c+(M+8) form: these c-carrying ARITH_RULEs
     rewrite 8*(k+1)+c+M to 8*k+c+(M+8) on the counters that carry c. *)
  REWRITE_TAC[ARITH_RULE `8 * (k + 1) + c = 8 * k + c + 8`;
              ARITH_RULE `8 * (k + 1) + c + 1 = 8 * k + c + 9`;
              ARITH_RULE `8 * (k + 1) + c + 2 = 8 * k + c + 10`;
              ARITH_RULE `8 * (k + 1) + c + 3 = 8 * k + c + 11`;
              ARITH_RULE `8 * (k + 1) + c + 4 = 8 * k + c + 12`;
              ARITH_RULE `8 * (k + 1) + c + 5 = 8 * k + c + 13`;
              ARITH_RULE `8 * (k + 1) + c + 6 = 8 * k + c + 14`;
              ARITH_RULE `8 * (k + 1) + c + 7 = 8 * k + c + 15`;
              ARITH_RULE `8 * (k + 1) + c + 8 = 8 * k + c + 16`] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[NONOVERLAPPING_CLAUSES] THEN ASM_ARITH_TAC);;

(* ========================================================================= *)
(* AES_GCM_ENC_ALT_FIXED_CORRECT_G1: the g = 1 leg (loop_count = 0, i.e.     *)
(* nblocks 9..16).  For g = 1 the main loop is skipped (the second setup     *)
(* guard, b.ge at 0x4bc, is taken and SETUP_G1 lands directly at pc+0xa10 =  *)
(* PREPRETAIL), so this is GEN_CORRECT's composition without the MAIN_LOOP   *)
(* sequence: SETUP_G1 -> PREPRETAIL_GEN (k = 0) -> TAIL_REM (g = 0+1, r =    *)
(* nb-8).  SETUP_G1's post at 0xa10 is GEN_CORRECT's second mid-state at     *)
(* k := 0, so all mid-states and ISPECLs are written in literal-0 form.  The *)
(* buffer bound `val in_p + 16*nb < 2 EXP 63` is carried for TAIL_REM.       *)
(* ========================================================================= *)
let AES_GCM_ENC_ALT_FIXED_CORRECT_G1 = prove
 (kterm `!in_p out_p tag_p ivec_p key_p htable_p stackpointer len_bits end_p
     tag0 nonce c rk inblock nb k pc.
    k = 0 /\
    8 * (0 + 1) <= nb /\
    len_bits = 128 * nb /\
    8 * (0 + 1) < nb /\ nb <= 8 * (0 + 2) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    end_p = word_add in_p (word (128 * (0 + 1))) /\
    val in_p + 128 * (0 + 1) < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (key_p, keybytes); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word len_bits /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (len_bits DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           wordlist_from_memory(key_p,nrk) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. read PC s = word (pc + pc_end) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN

  (* ===== SEQUENCE 1: SETUP_G1  pc+0x38 -> pc+0xa10 (skips main loop) ===== *)
  ENSURES_SEQUENCE_TAC (kterm `pc + pc_prepretail`)
   (kterm `\s. read X0 s = word_add in_p (word (128 * (0 + 1))) /\
        read X2 s = word_add out_p (word (128 * (0 + 1))) /\
        read X3 s = tag_p /\
        read X9 s = word (16 * nb) /\
        read X4 s = word_add in_p (word (16 * nb)) /\
        read X16 s = ivec_p /\
        read X5 s = end_p /\
        read X6 s = htable_p /\
        read X10 s = word_add stackpointer (word 0x40) /\
        read X11 s = key_p /\
        read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
          word 0xc200000000000000 /\
        wordlist_from_memory(key_p,nrk) s = MAP (word_reversefields 8) rk /\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
        read (memory :> bytes128 ivec_p) s =
          word_reversefields 8 (ctr_block nonce c) /\
        read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + c + 13)) /\
        read Q31 s = word 79228162514264337593543950336 /\
        read Q19 s =
          nist_ghash (cipher (word 0) rk) tag0
              (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8 * 0)) /\
        read Q8 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 0))) (inblock (8 * 0 + 0)) /\
        read Q9 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 1))) (inblock (8 * 0 + 1)) /\
        read Q10 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 2))) (inblock (8 * 0 + 2)) /\
        read Q11 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 3))) (inblock (8 * 0 + 3)) /\
        read Q12 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 4))) (inblock (8 * 0 + 4)) /\
        read Q13 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 5))) (inblock (8 * 0 + 5)) /\
        read Q14 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 6))) (inblock (8 * 0 + 6)) /\
        read Q15 s = word_xor (aes_ctr_block cipher c nonce rk ((8 * 0 + 7))) (inblock (8 * 0 + 7)) /\
        read Q0 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 8)) /\
        read Q1 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 9)) /\
        read Q2 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 10)) /\
        read Q3 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 11)) /\
        read Q4 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 12)) /\
        htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
        (!j. j < nb
             ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                 inblock j) /\
        (!j. j < 8 * (0 + 1)
             ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                 word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j))`) THEN
  CONJ_TAC THENL
   [(* SETUP leg *)
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
      MAYCHANGE [memory :> bytes(out_p, 16 * nb)]` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
              MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
      SUBSUMED_MAYCHANGE_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
      `key_p:int64`; `htable_p:int64`; `stackpointer:int64`; `len_bits:num`;
      `end_p:int64`; `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`;
      `inblock:num->int128`; `nb:num`; `0`; `pc:num`]
     AES_GCM_ENC_ALT_SETUP_G1) THEN
    REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[NONOVERLAPPING_CLAUSES] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN

  (* ============ SEQUENCE 3: PREPRETAIL  pc+0xa10 -> pc+0xee0 ============  *)
  (* The same existential Q18/Q27 mid-state as in GEN_CORRECT.               *)
  ENSURES_SEQUENCE_TAC (kterm `pc + pc_tail`)
   (kterm `\s. ?v18 v27.
        read Q18 s = v18 /\ read Q27 s = v27 /\
        read X0 s = word_add in_p (word (128 * (0 + 1))) /\
        read X2 s = word_add out_p (word (128 * (0 + 1))) /\
        read X3 s = tag_p /\
        read X9 s = word (16 * nb) /\
        read X4 s = word_add in_p (word (16 * nb)) /\
        read X16 s = ivec_p /\
        read X5 s = end_p /\
        read X6 s = htable_p /\
        read X10 s = word_add stackpointer (word 0x40) /\
        read X11 s = key_p /\
        read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
          word 0xc200000000000000 /\
        wordlist_from_memory(key_p,nrk) s = MAP (word_reversefields 8) rk /\
        read (memory :> bytes128 ivec_p) s =
          word_reversefields 8 (ctr_block nonce c) /\
        read Q28 s = word_reversefields 8 (EL nr rk) /\
        read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + c + 16)) /\
        read Q31 s = word 79228162514264337593543950336 /\
        read Q19 s =
          nist_ghash (cipher (word 0) rk) tag0
              (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8 * (0 + 1))) /\
        word_xor (read Q0 s) (word_reversefields 8 (EL nr rk)) =
          word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 8)) rk) /\
        word_xor (read Q1 s) (word_reversefields 8 (EL nr rk)) =
          word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 9)) rk) /\
        word_xor (read Q2 s) (word_reversefields 8 (EL nr rk)) =
          word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 10)) rk) /\
        word_xor (read Q3 s) (word_reversefields 8 (EL nr rk)) =
          word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 11)) rk) /\
        word_xor (read Q4 s) (word_reversefields 8 (EL nr rk)) =
          word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 12)) rk) /\
        word_xor (read Q5 s) (word_reversefields 8 (EL nr rk)) =
          word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 13)) rk) /\
        word_xor (read Q6 s) (word_reversefields 8 (EL nr rk)) =
          word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 14)) rk) /\
        word_xor (read Q7 s) (word_reversefields 8 (EL nr rk)) =
          word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 15)) rk) /\
        htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
        (!j. j < nb
             ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                 inblock j) /\
        (!j. j < 8 * (0 + 1)
             ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                 word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j))`) THEN
  CONJ_TAC THENL
   [(* PREPRETAIL leg, as in GEN_CORRECT. *)
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
      MAYCHANGE [memory :> bytes(out_p, 16 * nb)]` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
              MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
      SUBSUMED_MAYCHANGE_TAC;
      ALL_TAC] THEN
    (* As in GEN_CORRECT: weaken the post to PREPRETAIL_GEN's full post. *)
    ENSURES_POSTCONDITION_TAC
     (kterm `\s. aligned_bytes_loaded s (word pc) tmc /\
          read PC s = word (pc + pc_tail) /\
          read X0 s = word_add in_p (word (128 * (0 + 1))) /\
          read X2 s = word_add out_p (word (128 * (0 + 1))) /\
          read X3 s = tag_p /\ read X9 s = word (16 * nb) /\ read X4 s = word_add in_p (word (16 * nb)) /\
          read X16 s = ivec_p /\ read X5 s = end_p /\ read X6 s = htable_p /\
          read X10 s = word_add stackpointer (word 0x40) /\ read X11 s = key_p /\
          read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
            word 0xc200000000000000 /\
          wordlist_from_memory(key_p,nrk) s = MAP (word_reversefields 8) rk /\
          read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
          read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce c) /\
          read Q28 s = word_reversefields 8 (EL nr rk) /\
          read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + c + 16)) /\
          read Q31 s = word 79228162514264337593543950336 /\
          read Q19 s = nist_ghash (cipher (word 0) rk) tag0
              (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8 * (0 + 1))) /\
          word_xor (read Q0 s) (word_reversefields 8 (EL nr rk)) =
            word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 8)) rk) /\
          word_xor (read Q1 s) (word_reversefields 8 (EL nr rk)) =
            word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 9)) rk) /\
          word_xor (read Q2 s) (word_reversefields 8 (EL nr rk)) =
            word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 10)) rk) /\
          word_xor (read Q3 s) (word_reversefields 8 (EL nr rk)) =
            word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 11)) rk) /\
          word_xor (read Q4 s) (word_reversefields 8 (EL nr rk)) =
            word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 12)) rk) /\
          word_xor (read Q5 s) (word_reversefields 8 (EL nr rk)) =
            word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 13)) rk) /\
          word_xor (read Q6 s) (word_reversefields 8 (EL nr rk)) =
            word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 14)) rk) /\
          word_xor (read Q7 s) (word_reversefields 8 (EL nr rk)) =
            word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 15)) rk) /\
          htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
          (!j. j < nb ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s = inblock j) /\
          (!j. j < 8 * (0 + 1) ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                 word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j))`) THEN
    CONJ_TAC THENL
     [(* (1) PP_post ==> Q_mid, as in GEN_CORRECT. *)
      X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN
      REPEAT(CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      EXISTS_TAC `read Q18 s:int128` THEN EXISTS_TAC `read Q27 s:int128` THEN
      ASM_REWRITE_TAC[];
      (* (2) PREPRETAIL_GEN applied. *)
      MP_TAC(ISPECL
       [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
        `key_p:int64`; `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
        `end_p:int64`; `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`;
        `inblock:num->int128`; `nb:num`; `0`; `pc:num`]
       AES_GCM_ENC_ALT_PREPRETAIL_GEN) THEN
      REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[NONOVERLAPPING_CLAUSES] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN

  (* ============ TAIL leg: pc+0xee0 -> pc+0x1154 ============               *)
  (* As in GEN_CORRECT: hoist the existential, then apply TAIL_REM.          *)
  REWRITE_TAC[GSYM RIGHT_EXISTS_AND_THM; GSYM LEFT_EXISTS_AND_THM] THEN
  MATCH_MP_TAC ENSURES_EXISTS2_PRECONDITION THEN
  MAP_EVERY X_GEN_TAC [`v18:int128`; `v27:int128`] THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC
   `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
    MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
    MAYCHANGE [memory :> bytes(out_p, 16 * nb);
               memory :> bytes(tag_p, 16);
               memory :> bytes(ivec_p, 16)]` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
            MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
    SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`v18:int128`; `v27:int128`;
    `in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
    `key_p:int64`; `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
    `end_p:int64`; `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`;
    `inblock:num->int128`; `nb:num`; `nb - 8 * (0 + 1)`; `0 + 1`; `pc:num`]
   AES_GCM_ENC_ALT_TAIL_REM) THEN
  REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  (* counter alignment (g := 0+1), as in GEN_CORRECT: these ARITH_RULEs
     rewrite 8*(0+1)+c+N to 8*0+c+(N+8). *)
  REWRITE_TAC[ARITH_RULE `8 * (0 + 1) + c = 8 * 0 + c + 8`;
              ARITH_RULE `8 * (0 + 1) + c + 1 = 8 * 0 + c + 9`;
              ARITH_RULE `8 * (0 + 1) + c + 2 = 8 * 0 + c + 10`;
              ARITH_RULE `8 * (0 + 1) + c + 3 = 8 * 0 + c + 11`;
              ARITH_RULE `8 * (0 + 1) + c + 4 = 8 * 0 + c + 12`;
              ARITH_RULE `8 * (0 + 1) + c + 5 = 8 * 0 + c + 13`;
              ARITH_RULE `8 * (0 + 1) + c + 6 = 8 * 0 + c + 14`;
              ARITH_RULE `8 * (0 + 1) + c + 7 = 8 * 0 + c + 15`;
              ARITH_RULE `8 * (0 + 1) + c + 8 = 8 * 0 + c + 16`] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[NONOVERLAPPING_CLAUSES] THEN ASM_ARITH_TAC);;

(* ========================================================================= *)
(* The legs for nb <= 8 (SETUP0_TAIL and FAST1..FAST4) and the core          *)
(* correctness theorem AES_GCM_ENC_ALT_CORRECT for every nb >= 1.            *)
(* ========================================================================= *)

(* ========================================================================= *)
(* SETUP0: the setup leg for nb in {5,6,7,8}.                                *)
(*                                                                           *)
(* For these nb (groups = (nb-1) DIV 8 = 0; nb <= 4 take the b.le to         *)
(* L256_enc_small, FAST1..FAST4) the b.ge at 0x44c is taken                  *)
(* (WB_BRANCH_COND_TRUE), so the main loop is skipped: the setup runs        *)
(* pc+0x38 -> pc+0xee0 (the tail entry), building the 8 CTR keystreams       *)
(* Q0..Q7 (counters c..c+7), the next counter Q30 = ctr_block nonce (c+8)    *)
(* and Q19 = the untouched GHASH accumulator = nist_ghash..[] = tag0.  This  *)
(* is the branch-taken analogue of SETUP_GEN (which falls through to the     *)
(* main loop).  The postcondition is the tail's precondition for g = 0       *)
(* (Q0..Q7 pre-rkn keystreams, Q30 = c+8, Q19 = tag0, X5 = in_p, the         *)
(* out-forall j < 0 vacuous), so TAIL_REM composes with it via               *)
(* ENSURES_SEQUENCE_TAC.                                                     *)
(*                                                                           *)
(* The drive is SETUP_GEN's up to the branch: NSTEP 1-7 (the b.le at step 7  *)
(* not taken), 8-261, then NSTEP 262 (the b.ge at 0x44c), which              *)
(* WB_BRANCH_COND_TRUE resolves to pc+0xee0.  Closers: the keystreams via    *)
(* KSCLOSE (CIPHER_RECONSTRUCT + the counter-lane reconstruction);           *)
(* Q30 via the lane lemma SETUP_Q30_LANES_10 + CTR_BLOCK_RECONSTRUCT_REV32;  *)
(* Q19 via NIST_GHASH_NIL; X4 via the word_ushr/MOD_LT bridge; X5 via        *)
(* WB_X5_GROUPS0.                                                            *)
(* ========================================================================= *)

(* KSCLOSE: the keystream closer.  The pre-rkn aese chain in register Qj,
   XORed with rkn, is rev8 (cipher (ctr_block nonce (c+j)) rk).  A
   direct `REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST` would have to
   bit-blast the 128-bit counter term, so the closer follows CIPHER_CLOSE's
   structural reconstruction (without its input-XOR reordering, since the
   keystream register is not XORed with an input block): fold the aese chain
   to cipher, reconstruct the AES-input counter lanes to ctr_block
   nonce K (CTR_LANE_LOW + CTR_NONCE_LANES + GSYM WORD_ADD +
   CTR_BLOCK_RECONSTRUCT_REV8/32, then cancel the double reverse), refold
   both sides to aes_ctr_block, and discharge the counter-index equality
   K = c+j by ARITH. *)
let KSCLOSE =
  ASM_REWRITE_TAC[CIPHER_RECONSTRUCT; MAP;
                  WORD_REVERSEFIELDS_REVERSEFIELDS; CIPHER_KEYLIST] THEN
  REWRITE_TAC[CTR_LANE_LOW; CTR_NONCE_LANES] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8; CTR_BLOCK_RECONSTRUCT_REV32] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[CIPHER_KEYLIST] THEN
  REWRITE_TAC[aes_ctr_block; ADD_CLAUSES] THEN
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
  TRY(REFL_TAC) THEN
  TRY(REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN ARITH_TAC);;

(* Shape-routed dispatcher for the SETUP0 (groups = 0) postcondition. *)
let SETUP0_DISPATCH : tactic = fun (asl,w as gl) ->
  if is_forall w then
    (* the input-forall (j<nb) and the vacuous out-forall (j<0) *)
    (REWRITE_TAC[ARITH_RULE `j < 8 * 0 <=> F`] THEN ASM_REWRITE_TAC[]) gl
  else if is_eq w then
    let l,r = dest_eq w in
    let rhd = try fst(dest_const(fst(strip_comb r))) with _ -> "?" in
    let lhd = try fst(dest_const(fst(strip_comb l))) with _ -> "?" in
    if rhd = "nist_ghash" then SETUP0_Q19_CLOSE gl
    else if lhd = "word_join" && rhd = "word_reversefields" then SETUP0_CTR_CLOSE gl
    else if lhd = "word_xor" then KSCLOSE gl
    else if lhd = "word_add" && rhd = "word_add" then
      (* X4: word_add in_p (word_ushr (word (128*nb)) 3) = in_p + 16*nb *)
      (AP_TERM_TAC THEN REWRITE_TAC[word_ushr; VAL_WORD; DIMINDEX_64] THEN
       AP_TERM_TAC THEN ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC) gl
    else if lhd = "word_add" then
      (* X5: word_add (round-down expr) in_p = in_p (via WB_X5_GROUPS0). *)
      ASM_SIMP_TAC[WB_X5_GROUPS0] gl
    else (* incl. the X9 count: word((128*nb) DIV 8) -> word(16*nb) *)
      ASM_REWRITE_TAC[ARITH_RULE `(128 * nb) DIV 8 = 16 * nb`] gl
  else ASM_REWRITE_TAC[] gl;;

let AES_GCM_ENC_ALT_SETUP0 = prove
 (kterm `!in_p out_p tag_p ivec_p key_p htable_p stackpointer len_bits
     tag0 nonce c rk inblock nb pc.
    1 <= nb /\ nb <= 8 /\ ~(nb = 2) /\ ~(nb = 4) /\ ~(nb = 1) /\ ~(nb = 3) /\
    len_bits = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb)]
      [(in_p, 16 * nb); (key_p, keybytes); (htable_p, 192);
       (tag_p, 16); (ivec_p, 16); (word_add stackpointer (word 0x40), 8)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word len_bits /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (len_bits DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           wordlist_from_memory(key_p,nrk) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + pc_tail) /\
           read X0 s = in_p /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = in_p /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X11 s = key_p /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           wordlist_from_memory(key_p,nrk) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q28 s = word_reversefields 8 (EL nr rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (c + 8)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block cipher c nonce rk inblock) 0) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce c) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (c + 2)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (c + 3)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (c + 4)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (c + 5)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (c + 6)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (c + 7)) rk) /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * 0
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb)])`,
  REWRITE_TAC[KEY_SPLIT] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALLPAIRS; ALL;
              NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES_GCM_ENC_ALT_EXEC]
      (kterm `LENGTH tmc`)]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_8; htable_mem_4]) THEN
  SUBGOAL_THEN `~(nb = 4)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `5 <= nb` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY NSTEP (1--5) THEN NSTEP 6 THEN NSTEP 7 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[
    MATCH_MP DISPATCH4_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 4)`));
    MATCH_MP DISPATCH_SMALL_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `5 <= nb`));
    COND_CLAUSES]) THEN
  MAP_EVERY NSTEP (8--36) THEN
  MAP_EVERY NSTEP (37--(setup_tail_branch-1)) THEN NSTEP setup_tail_branch THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP WB_BRANCH_COND_TRUE
     (CONJ (ASSUME `1 <= nb`) (ASSUME `nb <= 8`)); COND_CLAUSES]) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[htable_mem_8; htable_mem_4] THEN REPEAT CONJ_TAC THEN SETUP0_DISPATCH);;

(* ========================================================================= *)
(* SETUP0_TAIL: the leg for nb in {5,6,7,8}, SETUP0 (pc+0x38 -> pc+0xee0)    *)
(* composed with TAIL_REM (r = nb, g = 0; pc+0xee0 -> pc+0x1154) by          *)
(* ENSURES_SEQUENCE_TAC at pc+0xee0: one tail group and no main loop (nb     *)
(* 1..4 are FAST1..FAST4).  Q18/Q27 are unpinned at SETUP0's exit, so the    *)
(* join uses the existential Q18/Q27 mid-state, as in the PREPRETAIL -> TAIL *)
(* join of GEN_CORRECT.                                                      *)
(* ========================================================================= *)
let AES_GCM_ENC_ALT_SETUP0_TAIL = prove
 (kterm `!in_p out_p tag_p ivec_p key_p htable_p stackpointer len_bits
     tag0 nonce c rk inblock nb pc.
    1 <= nb /\ nb <= 8 /\ ~(nb = 2) /\ ~(nb = 4) /\ ~(nb = 1) /\ ~(nb = 3) /\
    len_bits = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (key_p, keybytes); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word len_bits /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (len_bits DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           wordlist_from_memory(key_p,nrk) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. read PC s = word (pc + pc_end) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN

  (* ===== SEQUENCE: SETUP0  pc+0x38 -> pc+0xee0 ===== *)
  ENSURES_SEQUENCE_TAC (kterm `pc + pc_tail`)
   (kterm `\s. ?v18 v27.
        read Q18 s = v18 /\ read Q27 s = v27 /\
           read X0 s = word_add in_p (word (128 * 0)) /\
           read X2 s = word_add out_p (word (128 * 0)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = word_add in_p (word (128 * 0)) /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X11 s = key_p /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s = word 0xc200000000000000 /\
           wordlist_from_memory(key_p,nrk) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q28 s = word_reversefields 8 (EL nr rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + c + 8)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block cipher c nonce rk inblock)
                              (8 * 0)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 2)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 3)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 4)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 5)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 6)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 7)) rk) /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * 0
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j))`) THEN
  CONJ_TAC THENL
   [(* SETUP0 leg *)
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
      MAYCHANGE [memory :> bytes(out_p, 16 * nb)]` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
              MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
      SUBSUMED_MAYCHANGE_TAC;
      ALL_TAC] THEN
    ENSURES_POSTCONDITION_TAC
     (kterm `      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + pc_tail) /\
           read X0 s = in_p /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = in_p /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X11 s = key_p /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           wordlist_from_memory(key_p,nrk) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q28 s = word_reversefields 8 (EL nr rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (c + 8)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block cipher c nonce rk inblock) 0) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce c) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (c + 2)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (c + 3)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (c + 4)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (c + 5)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (c + 6)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (c + 7)) rk) /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * 0
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))`) THEN
    CONJ_TAC THENL
     [X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0]) THEN
      REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
      REPEAT(CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      EXISTS_TAC `read Q18 s:int128` THEN EXISTS_TAC `read Q27 s:int128` THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL
       [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
        `key_p:int64`; `htable_p:int64`; `stackpointer:int64`; `len_bits:num`;
        `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`;
        `inblock:num->int128`; `nb:num`; `pc:num`]
       AES_GCM_ENC_ALT_SETUP0) THEN
      REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[NONOVERLAPPING_CLAUSES] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN

  (* ===== TAIL leg: pc+0xee0 -> pc+0x1154 ===== *)
  REWRITE_TAC[GSYM RIGHT_EXISTS_AND_THM; GSYM LEFT_EXISTS_AND_THM] THEN
  MATCH_MP_TAC ENSURES_EXISTS2_PRECONDITION THEN
  MAP_EVERY X_GEN_TAC [`v18:int128`; `v27:int128`] THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC
   `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
    MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
    MAYCHANGE [memory :> bytes(out_p, 16 * nb);
               memory :> bytes(tag_p, 16);
               memory :> bytes(ivec_p, 16)]` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
            MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
    SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`v18:int128`; `v27:int128`;
    `in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
    `key_p:int64`; `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
    `word_add in_p (word (128 * 0)):int64`;
    `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`;
    `inblock:num->int128`; `nb:num`; `nb:num`; `0`; `pc:num`]
   AES_GCM_ENC_ALT_TAIL_REM) THEN
  REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[NONOVERLAPPING_CLAUSES] THEN
  ASM_ARITH_TAC);;

(* FAST2: the nb = 2 (32-byte) leg, pc+0x38 -> pc+0x1154, through the small  *)
(* path.  ENSURES_SEQUENCE at 0x17d4: segment A is the dispatch (the b.le at *)
(* 0x50 taken, the small_1 test falling through and the small_2 test at      *)
(* 0x1534/0x1538 taken, DISPATCH_TAKEN) and the 2-block AES; segment B is    *)
(* FAST2_TAIL.  The split is at 0x17d4, where the tail starts, so that the   *)
(* tail's eor3 write of the block-0 ciphertext is tracked from a             *)
(* fresh entry.                                                              *)
(* ========================================================================= *)
let FAST2_MID_D2 : tactic = fun (asl,w as gl) ->
  if is_forall w then
    ((GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC) ORELSE
     REWRITE_TAC[ARITH_RULE `8 * 0 = 0`; ARITH_RULE `!j:num. j < 0 <=> F`]) gl
  else if is_eq w then
    let l,r = dest_eq w in
    let rhd = try fst(dest_const(fst(strip_comb r))) with _ -> "?" in
    let lhd = try fst(dest_const(fst(strip_comb l))) with _ -> "?" in
    if lhd = "word_xor" then (FIRST_ASSUM ACCEPT_TAC ORELSE KSCLOSE) gl
    else
      (FIRST_ASSUM ACCEPT_TAC ORELSE
       (ASM_REWRITE_TAC[ARITH_RULE `(128 * nb) DIV 8 = 16 * nb`] THEN
        (if rhd = "nist_ghash" then SETUP0_Q19_CLOSE
         else if rhd = "word_reversefields" then SETUP0_CTR_CLOSE
         else if rhd = "word_add" then
            (REWRITE_TAC[ARITH_RULE `128 * 0 = 0`; WORD_ADD_0] THEN REFL_TAC)
         (* Q12 index closer *)
         else (REFL_TAC ORELSE CONV_TAC WORD_BLAST)))) gl
  else (REWRITE_TAC[htable_mem_8; htable_mem_4] THEN ASM_REWRITE_TAC[]) gl;;
let AES_GCM_ENC_ALT_FAST2 = prove
 (kterm `!in_p out_p tag_p ivec_p key_p htable_p stackpointer len_bits
     tag0 nonce c rk inblock nb pc.
    nb = 2 /\
    len_bits = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (key_p, keybytes); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word len_bits /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (len_bits DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           wordlist_from_memory(key_p,nrk) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. read PC s = word (pc + pc_end) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[KEY_SPLIT] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[LENGTH_WB_MC; htable_mem_8; htable_mem_4; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_SEQUENCE_TAC (kterm `pc + pc_fast2`)
   (kterm `\s. read X0 s = word_add in_p (word (128 * 0)) /\
           read X2 s = word_add out_p (word (128 * 0)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X16 s = ivec_p /\
           read Q12 s = word 0x000102030405060708090a0b0c0d0e0f /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s = word 0xc200000000000000 /\
           word_xor (read Q0 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 1)) rk) /\
           read Q19 s =
             nist_ghash (cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8 * 0)) /\
           read Q28 s = word_reversefields 8 (EL nr rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + c + 2)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * 0
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j))`) THEN
  CONJ_TAC THENL
   [(* Segment A: 0x38 -> 0x17d4 *)
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES_GCM_ENC_ALT_EXEC]
      (kterm `LENGTH tmc`)]) THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 0)))) s0 = inblock 0`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 1)))) s0 = inblock 1`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 4)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `1 <= nb` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `nb <= 3` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 1)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY NSTEP (1--5) THEN NSTEP 6 THEN NSTEP 7 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[
      MATCH_MP DISPATCH4_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 4)`));
      MATCH_MP DISPATCH_SMALL_TAKEN (CONJ (ASSUME `1 <= nb`) (ASSUME `nb <= 3`)); COND_CLAUSES]) THEN
    MAP_EVERY NSTEP (8--25) THEN
    NSTEP 26 THEN NSTEP 27 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH1_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 1)`)); COND_CLAUSES]) THEN
    NSTEP 28 THEN NSTEP 29 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH_TAKEN (ASSUME `nb = 2`); COND_CLAUSES]) THEN
    MAP_EVERY NSTEP (30--fast2_steps) THEN
    SUBGOAL_THEN
     (kterm `word_xor (read Q0 sfast2) (word_reversefields 8 (EL nr rk)) =
      word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c)) rk)`)
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    SUBGOAL_THEN
     (kterm `word_xor (read Q1 sfast2) (word_reversefields 8 (EL nr rk)) =
      word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 1)) rk)`)
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN
    REPEAT CONJ_TAC THEN FAST2_MID_D2;
    (* Segment B: 0x17d4 -> 0x1154 = FAST2_TAIL *)
    MP_TAC(ISPECL
     [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
      `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
      `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`; `inblock:num->int128`;
      `nb:num`; `0`; `pc:num`] AES_GCM_ENC_ALT_FAST2_TAIL) THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                LENGTH_WB_MC; htable_mem_8; htable_mem_4; ALLPAIRS; PAIRWISE; ALL;
                NONOVERLAPPING_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE CONV_TAC WORD_RULE ORELSE
     ASM_REWRITE_TAC[])]);;

(* ========================================================================= *)
(* FAST4: the nb = 4 (64-byte) leg, entry pc+0x38.  As FAST2 but for 4       *)
(* blocks: the b.le at 0x50 is taken (DISPATCH4_TAKEN) and the small_1/2/3   *)
(* `b.eq` tests fall through (nb <> 1,2,3) to L256_enc_small_4 (0x1544), the *)
(* 4-block AES (blocks 0-3); ENSURES_SEQUENCE splits at 0x15ac (the small_4  *)
(* tail start, with the keystreams as preconditions) into FAST4_TAIL.        *)
(* ========================================================================= *)
let AES_GCM_ENC_ALT_FAST4 = prove
 (kterm `!in_p out_p tag_p ivec_p key_p htable_p stackpointer len_bits
     tag0 nonce c rk inblock nb pc.
    nb = 4 /\
    len_bits = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (key_p, keybytes); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word len_bits /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (len_bits DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           wordlist_from_memory(key_p,nrk) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. read PC s = word (pc + pc_end) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[KEY_SPLIT] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[LENGTH_WB_MC; htable_mem_8; htable_mem_4; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_SEQUENCE_TAC (kterm `pc + pc_fast4`)
   (kterm `\s. read X0 s = word_add in_p (word (128 * 0)) /\
           read X2 s = word_add out_p (word (128 * 0)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X16 s = ivec_p /\
           read Q12 s = word 0x000102030405060708090a0b0c0d0e0f /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s = word 0xc200000000000000 /\
           word_xor (read Q0 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 2)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 3)) rk) /\
           read Q19 s =
             nist_ghash (cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8 * 0)) /\
           read Q28 s = word_reversefields 8 (EL nr rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + c + 4)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * 0
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j))`) THEN
  CONJ_TAC THENL
   [(* Segment A: 0x38 -> 0x15ac (dispatch + 4-block AES) *)
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES_GCM_ENC_ALT_EXEC]
      (kterm `LENGTH tmc`)]) THEN
    SUBGOAL_THEN `~(nb = 2)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 0)))) s0 = inblock 0`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 1)))) s0 = inblock 1`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 1)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 3)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY NSTEP (1--5) THEN NSTEP 6 THEN NSTEP 7 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH4_TAKEN (ASSUME `nb = 4`); COND_CLAUSES]) THEN
    MAP_EVERY NSTEP (8--25) THEN
    NSTEP 26 THEN NSTEP 27 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH1_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 1)`)); COND_CLAUSES]) THEN
    NSTEP 28 THEN NSTEP 29 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 2)`)); COND_CLAUSES]) THEN
    NSTEP 30 THEN NSTEP 31 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH3_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 3)`)); COND_CLAUSES]) THEN
    MAP_EVERY NSTEP (32--fast4_steps) THEN
    SUBGOAL_THEN
     (kterm `word_xor (read Q0 sfast4) (word_reversefields 8 (EL nr rk)) =
      word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c)) rk)`)
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    SUBGOAL_THEN
     (kterm `word_xor (read Q1 sfast4) (word_reversefields 8 (EL nr rk)) =
      word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 1)) rk)`)
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    SUBGOAL_THEN
     (kterm `word_xor (read Q2 sfast4) (word_reversefields 8 (EL nr rk)) =
      word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 2)) rk)`)
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    SUBGOAL_THEN
     (kterm `word_xor (read Q3 sfast4) (word_reversefields 8 (EL nr rk)) =
      word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 3)) rk)`)
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN
    REPEAT CONJ_TAC THEN FAST2_MID_D2;
    (* Segment B: 0x15ac -> 0x1154 = FAST4_TAIL *)
    MP_TAC(ISPECL
     [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
      `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
      `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`; `inblock:num->int128`;
      `nb:num`; `0`; `pc:num`] AES_GCM_ENC_ALT_FAST4_TAIL) THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                LENGTH_WB_MC; htable_mem_8; htable_mem_4; ALLPAIRS; PAIRWISE; ALL;
                NONOVERLAPPING_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE CONV_TAC WORD_RULE ORELSE
     ASM_REWRITE_TAC[])]);;

(* ========================================================================= *)
(* FAST1: the nb = 1 (16-byte) leg, entry pc+0x38.  The b.le to              *)
(* L256_enc_small is taken (nb <= 4) and the first test there, `b.eq         *)
(* L256_enc_small_1` at 0x1530, is taken (nb = 1) -> 1-block AES (block 0    *)
(* only); ENSURES_SEQUENCE splits at 0x187c (the small_1 tail start, with    *)
(* the keystream Q0 as precondition) into FAST1_TAIL.                        *)
(* ========================================================================= *)
let AES_GCM_ENC_ALT_FAST1 = prove
 (kterm `!in_p out_p tag_p ivec_p key_p htable_p stackpointer len_bits
     tag0 nonce c rk inblock nb pc.
    nb = 1 /\
    len_bits = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (key_p, keybytes); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word len_bits /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (len_bits DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           wordlist_from_memory(key_p,nrk) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. read PC s = word (pc + pc_end) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[KEY_SPLIT] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[LENGTH_WB_MC; htable_mem_8; htable_mem_4; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_SEQUENCE_TAC (kterm `pc + pc_fast1`)
   (kterm `\s. read X0 s = word_add in_p (word (128 * 0)) /\
           read X2 s = word_add out_p (word (128 * 0)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X16 s = ivec_p /\
           read Q12 s = word 0x000102030405060708090a0b0c0d0e0f /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s = word 0xc200000000000000 /\
           word_xor (read Q0 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c)) rk) /\
           read Q19 s =
             nist_ghash (cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8 * 0)) /\
           read Q28 s = word_reversefields 8 (EL nr rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + c + 1)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * 0
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j))`) THEN
  CONJ_TAC THENL
   [(* Segment A: 0x38 -> 0x187c (dispatch + 1-block AES) *)
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES_GCM_ENC_ALT_EXEC]
      (kterm `LENGTH tmc`)]) THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 0)))) s0 = inblock 0`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 2)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 4)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `1 <= nb` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `nb <= 3` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY NSTEP (1--5) THEN NSTEP 6 THEN NSTEP 7 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[
      MATCH_MP DISPATCH4_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 4)`));
      MATCH_MP DISPATCH_SMALL_TAKEN (CONJ (ASSUME `1 <= nb`) (ASSUME `nb <= 3`)); COND_CLAUSES]) THEN
    MAP_EVERY NSTEP (8--25) THEN
    NSTEP 26 THEN NSTEP 27 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH1_TAKEN (ASSUME `nb = 1`); COND_CLAUSES]) THEN
    MAP_EVERY NSTEP (28--fast1_steps) THEN
    SUBGOAL_THEN
     (kterm `word_xor (read Q0 sfast1) (word_reversefields 8 (EL nr rk)) =
      word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c)) rk)`)
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN
    REPEAT CONJ_TAC THEN FAST2_MID_D2;
    (* Segment B: 0x187c -> FAST1_TAIL *)
    MP_TAC(ISPECL
     [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
      `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
      `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`; `inblock:num->int128`;
      `nb:num`; `0`; `pc:num`] AES_GCM_ENC_ALT_FAST1_TAIL) THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                LENGTH_WB_MC; htable_mem_8; htable_mem_4; ALLPAIRS; PAIRWISE; ALL;
                NONOVERLAPPING_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE CONV_TAC WORD_RULE ORELSE
     ASM_REWRITE_TAC[])]);;

(* ========================================================================= *)
(* FAST3: the nb = 3 (48-byte) leg, entry pc+0x38.  The small_1 and small_2  *)
(* `b.eq` tests fall through (nb <> 1, 2) and the small_3 test `cmp          *)
(* x9,#0x30; b.eq L256_enc_small_3` at 0x153c/0x1540 is taken (nb = 3) ->    *)
(* 3-block AES; ENSURES_SEQUENCE splits at 0x16ec (the small_3 tail start,   *)
(* with the 3 keystreams as preconditions) into FAST3_TAIL.                  *)
(* ========================================================================= *)
let AES_GCM_ENC_ALT_FAST3 = prove
 (kterm `!in_p out_p tag_p ivec_p key_p htable_p stackpointer len_bits
     tag0 nonce c rk inblock nb pc.
    nb = 3 /\
    len_bits = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (key_p, keybytes); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word len_bits /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (len_bits DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           wordlist_from_memory(key_p,nrk) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. read PC s = word (pc + pc_end) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[KEY_SPLIT] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[LENGTH_WB_MC; htable_mem_8; htable_mem_4; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_SEQUENCE_TAC (kterm `pc + pc_fast3`)
   (kterm `\s. read X0 s = word_add in_p (word (128 * 0)) /\
           read X2 s = word_add out_p (word (128 * 0)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X16 s = ivec_p /\
           read Q12 s = word 0x000102030405060708090a0b0c0d0e0f /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s = word 0xc200000000000000 /\
           word_xor (read Q0 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL nr rk)) =
             word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 2)) rk) /\
           read Q19 s =
             nist_ghash (cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block cipher c nonce rk inblock) (8 * 0)) /\
           read Q28 s = word_reversefields 8 (EL nr rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + c + 3)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * 0
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j))`) THEN
  CONJ_TAC THENL
   [(* Segment A: 0x38 -> 0x16ec (dispatch + 3-block AES) *)
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES_GCM_ENC_ALT_EXEC]
      (kterm `LENGTH tmc`)]) THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 0)))) s0 = inblock 0`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 1)))) s0 = inblock 1`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 2)))) s0 = inblock 2`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 2)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 4)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 1)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `1 <= nb` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `nb <= 3` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY NSTEP (1--5) THEN NSTEP 6 THEN NSTEP 7 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[
      MATCH_MP DISPATCH4_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 4)`));
      MATCH_MP DISPATCH_SMALL_TAKEN (CONJ (ASSUME `1 <= nb`) (ASSUME `nb <= 3`)); COND_CLAUSES]) THEN
    MAP_EVERY NSTEP (8--25) THEN
    NSTEP 26 THEN NSTEP 27 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH1_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 1)`)); COND_CLAUSES]) THEN
    NSTEP 28 THEN NSTEP 29 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 2)`)); COND_CLAUSES]) THEN
    NSTEP 30 THEN NSTEP 31 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH3_TAKEN (ASSUME `nb = 3`); COND_CLAUSES]) THEN
    MAP_EVERY NSTEP (32--fast3_steps) THEN
    SUBGOAL_THEN
     (kterm `word_xor (read Q0 sfast3) (word_reversefields 8 (EL nr rk)) =
      word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c)) rk)`)
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    SUBGOAL_THEN
     (kterm `word_xor (read Q1 sfast3) (word_reversefields 8 (EL nr rk)) =
      word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 1)) rk)`)
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    SUBGOAL_THEN
     (kterm `word_xor (read Q2 sfast3) (word_reversefields 8 (EL nr rk)) =
      word_reversefields 8 (cipher (ctr_block nonce (8 * 0 + c + 2)) rk)`)
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN
    REPEAT CONJ_TAC THEN FAST2_MID_D2;
    (* Segment B: 0x16ec -> FAST3_TAIL *)
    MP_TAC(ISPECL
     [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
      `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
      `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`; `inblock:num->int128`;
      `nb:num`; `0`; `pc:num`] AES_GCM_ENC_ALT_FAST3_TAIL) THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                LENGTH_WB_MC; htable_mem_8; htable_mem_4; ALLPAIRS; PAIRWISE; ALL;
                NONOVERLAPPING_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE CONV_TAC WORD_RULE ORELSE
     ASM_REWRITE_TAC[])]);;

let AES_GCM_ENC_ALT_CORRECT = prove
 (kterm `!in_p out_p tag_p ivec_p key_p htable_p stackpointer len_bits
     tag0 nonce c rk inblock nb pc.
    1 <= nb /\
    len_bits = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (key_p, keybytes); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word len_bits /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (len_bits DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           wordlist_from_memory(key_p,nrk) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. read PC s = word (pc + pc_end) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `nb <= 8 \/ (9 <= nb /\ nb <= 16) \/ 17 <= nb` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THENL
   [(* ===== g = 0  (nb 1..8) ===== *)
    ASM_CASES_TAC `nb = 1` THENL
     [(* nb = 1 (16B): the fast1 early-dispatch path *)
      MP_TAC(ISPECL
       [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
        `key_p:int64`; `htable_p:int64`; `stackpointer:int64`; `len_bits:num`;
        `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`;
        `inblock:num->int128`; `nb:num`; `pc:num`]
       AES_GCM_ENC_ALT_FAST1) THEN
      REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
      DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
      (NONOVERLAPPING_TAC ORELSE CONV_TAC WORD_RULE ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[]);
    ASM_CASES_TAC `nb = 2` THENL
     [(* nb = 2 (32B): the fast2 early-dispatch path *)
      MP_TAC(ISPECL
       [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
        `key_p:int64`; `htable_p:int64`; `stackpointer:int64`; `len_bits:num`;
        `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`;
        `inblock:num->int128`; `nb:num`; `pc:num`]
       AES_GCM_ENC_ALT_FAST2) THEN
      REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
      DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
      (NONOVERLAPPING_TAC ORELSE CONV_TAC WORD_RULE ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[]);
      ASM_CASES_TAC `nb = 3` THENL
       [(* nb = 3 (48B): the fast3 early-dispatch path *)
        MP_TAC(ISPECL
         [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
          `key_p:int64`; `htable_p:int64`; `stackpointer:int64`; `len_bits:num`;
          `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`;
          `inblock:num->int128`; `nb:num`; `pc:num`]
         AES_GCM_ENC_ALT_FAST3) THEN
        REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
        DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
        (NONOVERLAPPING_TAC ORELSE CONV_TAC WORD_RULE ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[]);
      (* nb <> 3: nb = 4 (FAST4) or nb in {5,6,7,8} (SETUP0_TAIL) *)
      ASM_CASES_TAC `nb = 4` THENL
       [(* nb = 4 (64B): the fast4 early-dispatch path *)
        MP_TAC(ISPECL
         [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
          `key_p:int64`; `htable_p:int64`; `stackpointer:int64`; `len_bits:num`;
          `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`;
          `inblock:num->int128`; `nb:num`; `pc:num`]
         AES_GCM_ENC_ALT_FAST4) THEN
        REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
        DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
        (NONOVERLAPPING_TAC ORELSE CONV_TAC WORD_RULE ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[]);
        (* nb in {5,6,7,8}: the generic 8-block path via SETUP0_TAIL *)
        MP_TAC(ISPECL
         [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
          `key_p:int64`; `htable_p:int64`; `stackpointer:int64`; `len_bits:num`;
          `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`;
          `inblock:num->int128`; `nb:num`; `pc:num`]
         AES_GCM_ENC_ALT_SETUP0_TAIL) THEN
        REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
        DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
        (NONOVERLAPPING_TAC ORELSE CONV_TAC WORD_RULE ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[])]]]];
    (* ===== g = 1  (nb 9..16): FIXED_CORRECT_G1 (k=0) ===== *)
    MP_TAC(ISPECL
     [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
      `key_p:int64`; `htable_p:int64`; `stackpointer:int64`; `len_bits:num`;
      `word_add in_p (word (128 * (0 + 1))):int64`;
      `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`;
      `inblock:num->int128`; `nb:num`; `0`; `pc:num`]
     AES_GCM_ENC_ALT_FIXED_CORRECT_G1) THEN
    REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
    (NONOVERLAPPING_TAC ORELSE CONV_TAC WORD_RULE ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[]);
    (* ===== g >= 2  (nb >= 17): GEN_CORRECT (k = groups-1) ===== *)
    MP_TAC(ISPECL
     [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
      `key_p:int64`; `htable_p:int64`; `stackpointer:int64`; `len_bits:num`;
      `word_add in_p (word (128 * (((nb - 1) DIV 8 - 1) + 1))):int64`;
      `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`;
      `inblock:num->int128`; `nb:num`; `(nb - 1) DIV 8 - 1`; `pc:num`]
     AES_GCM_ENC_ALT_GEN_CORRECT) THEN
    REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN MP_TAC(SPECL [`nb - 1`; `8`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
    ABBREV_TAC `q = (nb - 1) DIV 8` THEN ABBREV_TAC `r = (nb - 1) MOD 8` THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THEN
    (NONOVERLAPPING_TAC ORELSE CONV_TAC WORD_RULE ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[])]);;

(* ------------------------------------------------------------------------- *)
(* The whole-block count actually processed, gcm_wb_blocks (shared, in       *)
(* aes_gcm_spec.ml), as a function of the bit length in X1.  The kernel has  *)
(* two entry guards: `cbz x1` for a zero length and `tst x1,#127` / `b.ne`   *)
(* for a length that is not a whole number of 128-bit blocks.  Both return 0 *)
(* without touching memory.  Folding that into the block count keeps one     *)
(* postcondition for all three paths, because at zero blocks the GHASH input *)
(* list is empty (so the tag is unchanged), the counter advances by 0, and   *)
(* the output forall is vacuous.                                             *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* AES_GCM_ENC_ALT_NOIBT_SUBROUTINE_CORRECT: the subroutine theorem, for     *)
(* every len_bits.  It lifts CORRECT through the two entry guards, the       *)
(* d8-d15 save/restore frame (80 bytes) and the final ret.                   *)
(*                                                                           *)
(* Wrapper shape:                                                            *)
(*   prologue 0x00 cbz x1,0x1170 ; 0x04 tst x1,#0x7f ; 0x08 b.ne 0x1170 ;    *)
(*     0x0c sub sp,sp,#0x50 ; stp d8,d9 ; lsr x9,x1,#3 ; mov x16,x4 ;        *)
(*     mov x11,x5 ; stp d10..d15 ; mov x5,#0xc2.. ; stp x5,xzr,[sp,#64] ;    *)
(*     add x10,sp,#0x40 ; 0x38 = the core entry (CORRECT);                   *)
(*   epilogue 0x1154 mov x0,x9 ; ldp d8..d15 ; add sp,sp,#0x50 ; 0x116c ret; *)
(*   reject 0x1170 mov w0,#0 ; ret (L256_enc_ret).                           *)
(* Entry C ABI: X0=in_p X1=len_bits X2=out_p X3=tag_p X4=ivec_p X5=key_p     *)
(* X6=htable_p; the prologue moves X4->X16 and X5->X11 and sets              *)
(* x9 = X1 >> 3.                                                             *)
(*                                                                           *)
(* The proof has three paths: a zero length (cbz x1 taken) and a length that *)
(* is not a multiple of 128 (tst/b.ne taken) both return 0 via L256_enc_ret; *)
(* only the main path, a nonzero whole number of blocks, falls through both  *)
(* guards (WB_GUARD1_NONZERO_GEN, WB_GUARD2_MASK_GEN) and runs CORRECT.      *)
(* ARM_ADD_RETURN_STACK_TAC is not used: its internal stepping of the        *)
(* prologue would meet the two conditional guards and leave a conditional    *)
(* PC, so the wrapper is assembled by hand.                                  *)
(* ------------------------------------------------------------------------- *)

let AES_GCM_ENC_ALT_NOIBT_SUBROUTINE_CORRECT = prove
 (kterm `!in_p out_p tag_p ivec_p key_p htable_p
     tag0 nonce c rk inblock len_bits pc stackpointer returnaddress.
    aligned 16 stackpointer /\
    val in_p + 16 * gcm_wb_blocks len_bits < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * gcm_wb_blocks len_bits); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 80), 80)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * gcm_wb_blocks len_bits); (key_p, keybytes);
       (htable_p, 192)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * gcm_wb_blocks len_bits); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 80), 80)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word pc /\
           read SP s = stackpointer /\
           read X30 s = returnaddress /\
           C_ARGUMENTS
            [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           wordlist_from_memory(key_p,nrk) s =
             MAP (word_reversefields 8) rk /\
           htable_mem_8 (ghash_twist (cipher (word 0) rk)) htable_p s /\
           (!j. j < gcm_wb_blocks len_bits
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. read PC s = returnaddress /\
           C_RETURN s = word (16 * gcm_wb_blocks len_bits) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (gcm_wb_blocks len_bits + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block cipher c nonce rk inblock)
                               (gcm_wb_blocks len_bits))) /\
           (!j. j < gcm_wb_blocks len_bits
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * gcm_wb_blocks len_bits);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16);
                  memory :> bytes(word_sub stackpointer (word 80), 80)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  (* Expand the compact round-key list, in place inside the precondition,    *)
  (* into the pointwise reads the interior legs consume.                     *)
  REWRITE_TAC[KEY_SPLIT] THEN
  REPEAT STRIP_TAC THEN
  (* Abbreviate the block count.  This is not cosmetic: keeping              *)
  (* `gcm_wb_blocks` folded stops `val len_bits = 128 * nb` from looping as  *)
  (* a rewrite, which it would if gcm_wb_blocks unfolded to `val len_bits    *)
  (* DIV 128` on the right.                                                  *)
  ABBREV_TAC `nb = gcm_wb_blocks len_bits` THEN
  ASM_CASES_TAC `val(len_bits:int64) MOD 128 = 0` THENL
   [ALL_TAC;
    (* ===================================================================== *)
    (* Path 3: the length is not a whole number of blocks.  `cbz x1` falls   *)
    (* through (a non-multiple of 128 is nonzero), `tst x1,#127` leaves ZF   *)
    (* clear so `b.ne` is taken, and L256_enc_ret returns 0.                 *)
    (* ===================================================================== *)
    SUBGOAL_THEN `nb = 0` SUBST_ALL_TAC THENL
     [EXPAND_TAC "nb" THEN REWRITE_TAC[gcm_wb_blocks] THEN
      ASM_REWRITE_TAC[COND_CLAUSES]; ALL_TAC] THEN
    (* The branch condition is phrased on `val len_bits`; derive that form. *)
    SUBGOAL_THEN `~(val(len_bits:int64) = 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `~(val(len_bits:int64) MOD 128 = 0)` THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    SUBGOAL_THEN `~(len_bits:int64 = word 0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[GSYM VAL_EQ_0]; ALL_TAC] THEN
    (* `tst x1,#127` leaves ZF clear, so `b.ne` is taken.  Both the word and *)
    (* the val form of the mask fact are needed to resolve the flag.         *)
    SUBGOAL_THEN `~(word_and (len_bits:int64) (word 0x7f) = word 0)`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[WB_MASK7_EQ_MOD]; ALL_TAC] THEN
    SUBGOAL_THEN `~(val(word_and (len_bits:int64) (word 0x7f)) = 0)`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[VAL_EQ_0]; ALL_TAC] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC AES_GCM_ENC_ALT_EXEC [1] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(val(len_bits:int64) = 0)`;
                               ASSUME `~(len_bits:int64 = word 0)`;
                               COND_CLAUSES]) THEN
    ARM_STEPS_TAC AES_GCM_ENC_ALT_EXEC [2] THEN
    ARM_STEPS_TAC AES_GCM_ENC_ALT_EXEC [3] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[
      ASSUME `~(word_and (len_bits:int64) (word 0x7f) = word 0)`;
      ASSUME `~(val(word_and (len_bits:int64) (word 0x7f)) = 0)`;
      COND_CLAUSES]) THEN
    ARM_STEPS_TAC AES_GCM_ENC_ALT_EXEC [4;5] THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[list_of_seq; nist_ghash] THEN
    REWRITE_TAC[ARITH_RULE `j < 0 <=> F`]] THEN
  (* From here on the length is a whole number of blocks. *)
  ASM_CASES_TAC `val(len_bits:int64) = 0` THENL
   [(* ===================================================================== *)
    (* Path 1: zero length.  `cbz x1` is taken straight to L256_enc_ret.     *)
    (* ===================================================================== *)
    SUBGOAL_THEN `nb = 0` SUBST_ALL_TAC THENL
     [EXPAND_TAC "nb" THEN REWRITE_TAC[gcm_wb_blocks] THEN
      ASM_REWRITE_TAC[COND_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    SUBGOAL_THEN `len_bits:int64 = word 0` SUBST_ALL_TAC THENL
     [ASM_REWRITE_TAC[GSYM VAL_EQ_0]; ALL_TAC] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC AES_GCM_ENC_ALT_EXEC [1;2;3] THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[list_of_seq; nist_ghash] THEN
    REWRITE_TAC[ARITH_RULE `j < 0 <=> F`];
    ALL_TAC] THEN
  (* ======================================================================= *)
  (* Path 2: a nonzero whole number of blocks.  Both guards fall through;    *)
  (* steps 1-14 are the prologue, the interior big step is _CORRECT, and     *)
  (* steps 16-22 are the epilogue (which sets X0 from X9).                   *)
  (* ======================================================================= *)
  SUBGOAL_THEN `1 <= nb` ASSUME_TAC THENL
   [EXPAND_TAC "nb" THEN REWRITE_TAC[gcm_wb_blocks] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`val(len_bits:int64)`; `128`] (CONJUNCT2 DIVISION_SIMP)) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(len_bits:int64) = 128 * nb` ASSUME_TAC THENL
   [EXPAND_TAC "nb" THEN ASM_SIMP_TAC[GCM_WB_BLOCKS_VALID]; ALL_TAC] THEN
  SUBGOAL_THEN `128 * nb < 2 EXP 64` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPEC `len_bits:int64` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC;
    ALL_TAC] THEN
  (* Put the length argument back into the constructed form `word (128 *     *)
  (* nb)`, the form WB_GUARD1_NONZERO_GEN and WB_GUARD2_MASK_GEN are stated  *)
  (* about, so that the guard lemmas apply directly, with no facts about an  *)
  (* opaque word and no rewrite that can loop.                               *)
  SUBGOAL_THEN `len_bits:int64 = word (128 * nb)` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if concl th = `val(len_bits:int64) = 128 * nb`
      then MP_TAC th else failwith "") THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[WORD_VAL];
    ALL_TAC] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun c -> ENSURES_PRESERVED_DREG_TAC ("init_"^fst(dest_const c)) c)
    [`D8`;`D9`;`D10`;`D11`;`D12`;`D13`;`D14`;`D15`] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_8; htable_mem_4]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(
    EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV THENC
    REWRITE_CONV[WORD_ADD_0]))) THEN
  ARM_STEPS_TAC AES_GCM_ENC_ALT_EXEC [1] THEN
  (* The `cbz x1` test reduces to the numeric form `128 * nb = 0` (the model *)
  (* simplifies `val(word(128*nb))` with the `128*nb < 2^64` fact), which    *)
  (* WB_GUARD1_NONZERO_GEN's word/val-shaped conjuncts do not rewrite;       *)
  (* discharge the numeric form directly from `1 <= nb` so that the          *)
  (* conditional PC collapses.                                               *)
  SUBGOAL_THEN `~(128 * nb = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `1 <= nb` THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP WB_GUARD1_NONZERO_GEN
    (CONJ (ASSUME `1 <= nb`) (ASSUME `128 * nb < 2 EXP 64`));
    ASSUME `~(128 * nb = 0)`;
    COND_CLAUSES]) THEN
  ARM_STEPS_TAC AES_GCM_ENC_ALT_EXEC [2] THEN
  ARM_STEPS_TAC AES_GCM_ENC_ALT_EXEC [3] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP WB_GUARD2_MASK_GEN
    (CONJ (ASSUME `1 <= nb`) (ASSUME `128 * nb < 2 EXP 64`));
    VAL_WORD_0; COND_CLAUSES]) THEN
  ARM_STEPS_TAC AES_GCM_ENC_ALT_EXEC (4--14) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP WB_X9_NORM
    (ASSUME `128 * nb < 2 EXP 64`)]) THEN
  MP_TAC(SPECL
   [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
    `key_p:int64`; `htable_p:int64`;
    `word_sub stackpointer (word 0x50):int64`;
    `128 * nb`;
    `tag0:int128`; `nonce:(96)word`; `c:num`;
    `rk:int128 list`;
    `inblock:num->int128`; `nb:num`; `pc:num`]
   (REWRITE_RULE[KEY_SPLIT] AES_GCM_ENC_ALT_CORRECT)) THEN
  REWRITE_TAC[LENGTH_WB_MC] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
    REPEAT CONJ_TAC THEN
    (NONOVERLAPPING_TAC ORELSE ASM_ARITH_TAC ORELSE CONV_TAC WORD_RULE ORELSE
     ASM_REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS]);
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              MODIFIABLE_SIMD_REGS; MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS;
              htable_mem_8; htable_mem_4] THEN
  ARM_BIGSTEP_TAC AES_GCM_ENC_ALT_EXEC "s15" THEN
  ARM_STEPS_TAC AES_GCM_ENC_ALT_EXEC (16--22) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_128; LE_REFL; ARITH] THEN
  CONV_TAC WORD_RULE);;

(* --- Core-level leg safety: FAST1..FAST4 (prove_fast_safe nb, for a fixed  *)
(* nb and so a fixed-length drive).                                          *)
(* Entry pc+0x38, exit pc+0x1154; MAYCHANGE frame (ABI, Q8..Q15,             *)
(* out/tag/ivec); f_events depends on the public pointers, stackpointer      *)
(* and pc.                                                                   *)

let prove_fast_safe n =
  prove
   (kterm(vsubst [mk_small_numeral n,`n:num`]
     `exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p stackpointer len_bits
     nb pc.
    nb = n /\
    len_bits = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (key_p, keybytes); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word len_bits /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (len_bits DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read events s = e)
      (\s. read PC s = word (pc + pc_end) /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events in_p out_p tag_p ivec_p key_p htable_p
                     stackpointer pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, keybytes;
                 htable_p, 192; word_add stackpointer (word 0x40), 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`),
    PROVE_SAFETY_SPEC_TAC AES_GCM_ENC_ALT_EXEC);;

let AES_GCM_ENC_ALT_FAST1_SAFE = prove_fast_safe 1;;
let AES_GCM_ENC_ALT_FAST2_SAFE = prove_fast_safe 2;;
let AES_GCM_ENC_ALT_FAST3_SAFE = prove_fast_safe 3;;
let AES_GCM_ENC_ALT_FAST4_SAFE = prove_fast_safe 4;;

(* --- Setup segment safety: SETUP0_SAFE (nb in {5,6,7,8}, pc+0x38 ->        *)
(* pc+0xee0).  It follows AES_GCM_ENC_ALT_SETUP0's stepping (NSTEP +         *)
(* DISPATCH4_NOT_TAKEN / DISPATCH_SMALL_NOT_TAKEN + WB_BRANCH_COND_TRUE) but *)
(* closes with the safety property.  The event trace is the same for every   *)
(* nb in {5,6,7,8}.                                                          *)
let AES_GCM_ENC_ALT_SETUP0_SAFE = prove
 (kterm `exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p stackpointer len_bits
     nb pc.
    1 <= nb /\ nb <= 8 /\ ~(nb = 1) /\ ~(nb = 2) /\ ~(nb = 3) /\ ~(nb = 4) /\
    len_bits = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (key_p, keybytes); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word len_bits /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (len_bits DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read events s = e)
      (\s. read PC s = word (pc + pc_tail) /\
           read X0 s = in_p /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = in_p /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X11 s = key_p /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events in_p out_p tag_p ivec_p key_p htable_p
                     stackpointer pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, keybytes;
                 htable_p, 192; word_add stackpointer (word 0x40), 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64)
      (key_p:int64) (htable_p:int64) (stackpointer:int64) (pc:num).
       f_ev in_p out_p tag_p ivec_p key_p htable_p stackpointer pc
       :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `~(nb = 4)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `5 <= nb` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY NSTEP (1--5) THEN NSTEP 6 THEN NSTEP 7 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[
    MATCH_MP DISPATCH4_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 4)`));
    MATCH_MP DISPATCH_SMALL_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `5 <= nb`));
    COND_CLAUSES]) THEN
  MAP_EVERY NSTEP (8--36) THEN
  MAP_EVERY NSTEP (37--(setup_tail_branch-1)) THEN NSTEP setup_tail_branch THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP WB_BRANCH_COND_TRUE
     (CONJ (ASSUME `1 <= nb`) (ASSUME `nb <= 8`)); COND_CLAUSES]) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY SETUP0_DISPATCH THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* --- Tail-cascade leg safety: TAIL_REM1..8_SAFE (entry pc+0xee0, exit      *)
(* pc+0x1154).  They follow AES_GCM_ENC_ALT_TAIL_REM<r>'s NSTEP_GP drive     *)
(* and TAIL_X5 branch resolution, but without the functional Q19-fold and    *)
(* data closers (safety needs only PC, events and inbounds), and close with  *)
(* the safety property.  Lean precondition: the key/htable/ivec/counter/     *)
(* inblock contents do not matter for safety (only the access addresses do), *)
(* so only the pointer registers are pinned.  nb = 8*g+r gives the rem = r   *)
(* arm; g is symbolic.  prove_tail_rem_safe r x5th steps proves the arm r,   *)
(* where x5th is TAIL_X5_REM<r> and the drive has steps instructions; the    *)
(* arm r = 8 (TAIL_X5_128_G, stated for 8*g+8 = nb) is proved separately.    *)

let prove_tail_rem_safe r x5th steps =
  prove
   (kterm(vsubst [mk_small_numeral r,`r:num`]
     `exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p mod_p end_p nb g pc.
    nb = 8 * g + r /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (key_p, keybytes); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + pc_tail) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read events s = e)
      (\s. read PC s = word (pc + pc_end) /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events in_p out_p tag_p ivec_p key_p htable_p mod_p g pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, keybytes;
                 htable_p, 192; mod_p, 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`),
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
                MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
    REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
    CONCRETIZE_F_EVENTS_TAC
      `\(in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64)
        (key_p:int64) (htable_p:int64) (mod_p:int64) (g:num) (pc:num).
         f_ev in_p out_p tag_p ivec_p key_p htable_p mod_p g pc
         :(uarch_event)list` THEN
    REPEAT META_EXISTS_TAC THEN
    REPEAT STRIP_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY NSTEP_GP (1--9) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[x5th]) THEN
    MAP_EVERY NSTEP_GP (10--steps) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC);;

let AES_GCM_ENC_ALT_TAIL_REM1_SAFE = prove_tail_rem_safe 1 TAIL_X5_REM1 85;;
let AES_GCM_ENC_ALT_TAIL_REM2_SAFE = prove_tail_rem_safe 2 TAIL_X5_REM2 57;;
let AES_GCM_ENC_ALT_TAIL_REM3_SAFE = prove_tail_rem_safe 3 TAIL_X5_REM3 110;;
let AES_GCM_ENC_ALT_TAIL_REM4_SAFE = prove_tail_rem_safe 4 TAIL_X5_REM4 110;;
let AES_GCM_ENC_ALT_TAIL_REM5_SAFE = prove_tail_rem_safe 5 TAIL_X5_REM5 119;;
let AES_GCM_ENC_ALT_TAIL_REM6_SAFE = prove_tail_rem_safe 6 TAIL_X5_REM6 127;;
let AES_GCM_ENC_ALT_TAIL_REM7_SAFE = prove_tail_rem_safe 7 TAIL_X5_REM7 133;;

let AES_GCM_ENC_ALT_TAIL_REM8_SAFE = prove
 (kterm `exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p mod_p end_p nb g pc.
    8 * g + 8 = nb /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (key_p, keybytes); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + pc_tail) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read events s = e)
      (\s. read PC s = word (pc + pc_end) /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events in_p out_p tag_p ivec_p key_p htable_p mod_p g pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, keybytes;
                 htable_p, 192; mod_p, 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64)
      (key_p:int64) (htable_p:int64) (mod_p:int64) (g:num) (pc:num).
       f_ev in_p out_p tag_p ivec_p key_p htable_p mod_p g pc
       :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP TAIL_X5_128_G (ASSUME `8 * g + 8 = nb`)]) THEN
  MAP_EVERY NSTEP_GP (10--119) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* --- Tail dispatch safety: TAIL_REM_SAFE (rem in 1..8, g >= 0).  It        *)
(* follows AES_GCM_ENC_ALT_TAIL_REM's r = 1 \/ .. \/ r = 8 case split:       *)
(* X_CHOOSE each arm's event-trace witness, give the explicit r-indexed      *)
(* dispatch function as f_events, then close each branch by the matching     *)
(* TAIL_REM<r>_SAFE.                                                         *)

let AES_GCM_ENC_ALT_TAIL_REM_SAFE = prove
 (kterm `exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p mod_p end_p nb r g pc.
    nb = 8 * g + r /\ 1 <= r /\ r <= 8 /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (key_p, keybytes); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + pc_tail) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read events s = e)
      (\s. read PC s = word (pc + pc_end) /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events r in_p out_p tag_p ivec_p key_p htable_p mod_p g pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, keybytes;
                 htable_p, 192; mod_p, 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  X_CHOOSE_TAC `w1:int64->int64->int64->int64->int64->int64->int64->num->num->(uarch_event)list` AES_GCM_ENC_ALT_TAIL_REM1_SAFE THEN
  X_CHOOSE_TAC `w2:int64->int64->int64->int64->int64->int64->int64->num->num->(uarch_event)list` AES_GCM_ENC_ALT_TAIL_REM2_SAFE THEN
  X_CHOOSE_TAC `w3:int64->int64->int64->int64->int64->int64->int64->num->num->(uarch_event)list` AES_GCM_ENC_ALT_TAIL_REM3_SAFE THEN
  X_CHOOSE_TAC `w4:int64->int64->int64->int64->int64->int64->int64->num->num->(uarch_event)list` AES_GCM_ENC_ALT_TAIL_REM4_SAFE THEN
  X_CHOOSE_TAC `w5:int64->int64->int64->int64->int64->int64->int64->num->num->(uarch_event)list` AES_GCM_ENC_ALT_TAIL_REM5_SAFE THEN
  X_CHOOSE_TAC `w6:int64->int64->int64->int64->int64->int64->int64->num->num->(uarch_event)list` AES_GCM_ENC_ALT_TAIL_REM6_SAFE THEN
  X_CHOOSE_TAC `w7:int64->int64->int64->int64->int64->int64->int64->num->num->(uarch_event)list` AES_GCM_ENC_ALT_TAIL_REM7_SAFE THEN
  X_CHOOSE_TAC `w8:int64->int64->int64->int64->int64->int64->int64->num->num->(uarch_event)list` AES_GCM_ENC_ALT_TAIL_REM8_SAFE THEN
  EXISTS_TAC
   `\(r:num) (in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64)
     (key_p:int64) (htable_p:int64) (mod_p:int64) (g:num) (pc:num).
      if r = 1 then w1 in_p out_p tag_p ivec_p key_p htable_p mod_p g pc
      else if r = 2 then w2 in_p out_p tag_p ivec_p key_p htable_p mod_p g pc
      else if r = 3 then w3 in_p out_p tag_p ivec_p key_p htable_p mod_p g pc
      else if r = 4 then w4 in_p out_p tag_p ivec_p key_p htable_p mod_p g pc
      else if r = 5 then w5 in_p out_p tag_p ivec_p key_p htable_p mod_p g pc
      else if r = 6 then w6 in_p out_p tag_p ivec_p key_p htable_p mod_p g pc
      else if r = 7 then w7 in_p out_p tag_p ivec_p key_p htable_p mod_p g pc
      else w8 in_p out_p tag_p ivec_p key_p htable_p mod_p g pc
      :(uarch_event)list` THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `in_p:int64`; `out_p:int64`; `tag_p:int64`;
    `ivec_p:int64`; `key_p:int64`; `htable_p:int64`; `mod_p:int64`;
    `end_p:int64`; `nb:num`; `r:num`; `g:num`; `pc:num`] THEN
  STRIP_TAC THEN
  BETA_TAC THEN
  SUBGOAL_THEN `r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7 \/ r = 8`
  MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && lhs(concl th) = `r:num`
    then SUBST_ALL_TAC th else failwith "not r-eq") THEN
  REWRITE_TAC[ARITH_EQ; COND_CLAUSES] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE
   (REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
    ASM_REWRITE_TAC[]) ORELSE
   CONV_TAC WORD_RULE));;

(* --- Whole-core safety for nb in {5,6,7,8}: SETUP0_TAIL_SAFE (pc+0x38 ->   *)
(* pc+0x1154).  Composes the strengthened SETUP0_SAFE (nb-independent setup  *)
(* segment, tail-entry registers in its post) with TAIL_REM_SAFE (g = 0,     *)
(* r = nb) by a double abstract bigstep: bigstep SETUP0_SAFE with e_tail =   *)
(* [] (its trace stays the abstract f_events_callee), then bigstep           *)
(* TAIL_REM_SAFE with e_tail = that abstract setup trace (a single term, so  *)
(* no CONS blowup).  f_events takes nb because the tail's event trace        *)
(* depends on nb (= r).                                                      *)
let AES_GCM_ENC_ALT_SETUP0_TAIL_SAFE = prove
 (kterm `exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p stackpointer len_bits
     nb pc.
    1 <= nb /\ nb <= 8 /\ ~(nb = 1) /\ ~(nb = 2) /\ ~(nb = 3) /\ ~(nb = 4) /\
    len_bits = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (key_p, keybytes); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word len_bits /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (len_bits DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read events s = e)
      (\s. read PC s = word (pc + pc_end) /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events nb in_p out_p tag_p ivec_p key_p htable_p
                     stackpointer pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, keybytes;
                 htable_p, 192; word_add stackpointer (word 0x40), 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC AES_GCM_ENC_ALT_TAIL_REM_SAFE "H_TAIL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC AES_GCM_ENC_ALT_SETUP0_SAFE "H_SETUP0" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(nb:num) (in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64)
      (key_p:int64) (htable_p:int64) (stackpointer:int64) (pc:num).
       APPEND
         (f_ev_tail nb in_p out_p tag_p ivec_p key_p htable_p stackpointer pc)
         (f_ev_setup in_p out_p tag_p ivec_p key_p htable_p stackpointer pc)
       :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
    MODIFIABLE_SIMD_REGS; MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS]) THEN
  (* ===== BIGSTEP 1: SETUP0 (pc+0x38 -> pc+0xee0), e_tail = [] ===== *)
  USE_THEN "H_SETUP0" (fun th ->
    MP_TAC (REWRITE_RULE[APPEND]
      (SPECL [`e:(uarch_event)list`; `in_p:int64`; `out_p:int64`; `tag_p:int64`;
              `ivec_p:int64`; `key_p:int64`; `htable_p:int64`; `stackpointer:int64`;
              `len_bits:num`; `nb:num`; `pc:num`; `[]:(uarch_event)list`] th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ARM_BIGSTEP_TAC AES_GCM_ENC_ALT_EXEC "s1" THEN
  (* ===== BIGSTEP 2: TAIL_REM (pc+0xee0 -> pc+0x1154), g=0, r=nb ===== *)
  USE_THEN "H_TAIL" (fun th ->
    MP_TAC (GEN_REWRITE_RULE I [RIGHT_FORALL_IMP_THM]
      (REWRITE_RULE[ARITH_RULE `128 * 0 = 0`; WORD_ADD_0]
        (SPECL [`e:(uarch_event)list`; `in_p:int64`; `out_p:int64`; `tag_p:int64`;
                `ivec_p:int64`; `key_p:int64`; `htable_p:int64`;
                `word_add stackpointer (word 0x40):int64`;
                `word_add in_p (word (128 * 0)):int64`;
                `nb:num`; `nb:num`; `0`; `pc:num`] th)))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
    REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[] ORELSE
     CONV_TAC WORD_RULE);
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM LEFT_EXISTS_IMP_THM] THEN
  META_EXISTS_TAC THEN
  ARM_BIGSTEP_TAC AES_GCM_ENC_ALT_EXEC "s2" THENL [
    BINOP_TAC THENL [ UNIFY_REFL_TAC; REFL_TAC ] THEN NO_TAC;
    ALL_TAC ] THEN
  (* ===== CLOSE ===== *)
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
  CONJ_TAC THENL
   [ BINOP_TAC THENL [ UNIFY_F_EVENTS_TAC; UNIFY_F_EVENTS_TAC ];
     DISCHARGE_MEMACCESS_INBOUNDS_TAC ])
;;

(* --- PREPRETAIL_GEN_SAFE (pc+0xa10 -> pc+0xee0): the shared prepretail     *)
(* segment (the reduction of the last full 8-block group) for nb >= 9.  Lean *)
(* spec (pointer registers only; content facts do not matter for safety).    *)
(* The pointer registers are unchanged from entry to exit; straight-line     *)
(* NSTEP_GP (1--prepretail_steps) drive.  f_events takes k (the access       *)
(* addresses depend on the group index).                                     *)
let AES_GCM_ENC_ALT_PREPRETAIL_GEN_SAFE = prove
 (kterm `exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p mod_p end_p nb k pc.
    8 * (k + 1) <= nb /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (key_p, keybytes); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + pc_prepretail) /\
           read X0 s = word_add in_p (word (128 * (k + 1))) /\
           read X2 s = word_add out_p (word (128 * (k + 1))) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read events s = e)
      (\s. read PC s = word (pc + pc_tail) /\
           read X0 s = word_add in_p (word (128 * (k + 1))) /\
           read X2 s = word_add out_p (word (128 * (k + 1))) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events in_p out_p tag_p ivec_p key_p htable_p mod_p k pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, keybytes;
                 htable_p, 192; mod_p, 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64)
      (key_p:int64) (htable_p:int64) (mod_p:int64) (k:num) (pc:num).
       f_ev in_p out_p tag_p ivec_p key_p htable_p mod_p k pc
       :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY NSTEP_GP (1--prepretail_steps) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC)
;;

(* --- SETUP_G1_SAFE (pc+0x38 -> pc+0xa10, k = 0, nb 9..16): the setup for   *)
(* the single-full-group case.  It follows SETUP_G1's NSTEP/LDP_SETUP_TAC    *)
(* drive and the SETUP_BRANCH_COND_FALSE_GEN / _TRUE_2 guard rewrites; the   *)
(* post is strengthened with the PREPRETAIL_GEN entry registers and closed   *)
(* via SETUP_RECON_TAC_GEN.                                                  *)
let AES_GCM_ENC_ALT_SETUP_G1_SAFE = prove
 (kterm `exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p stackpointer len_bits end_p
     nb k pc.
    k = 0 /\
    8 * (k + 1) <= nb /\
    len_bits = 128 * nb /\
    8 * (k + 1) < nb /\ nb <= 8 * (k + 2) /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (key_p, keybytes); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word len_bits /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (len_bits DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read events s = e)
      (\s. read PC s = word (pc + pc_prepretail) /\
           read X0 s = word_add in_p (word (128 * (0 + 1))) /\
           read X2 s = word_add out_p (word (128 * (0 + 1))) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X11 s = key_p /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events in_p out_p tag_p ivec_p key_p htable_p
                     stackpointer pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, keybytes;
                 htable_p, 192; word_add stackpointer (word 0x40), 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64)
      (key_p:int64) (htable_p:int64) (stackpointer:int64) (pc:num).
       f_ev in_p out_p tag_p ivec_p key_p htable_p stackpointer pc
       :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN
   `?inblock. !j. j < nb
      ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s0 =
          inblock j`
   (CHOOSE_THEN ASSUME_TAC) THENL
   [EXISTS_TAC
      `\j. read (memory :> bytes128 (word_add in_p (word (16 * j)))) s0` THEN
    REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(nb = 4)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `5 <= nb` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY NSTEP (1--5) THEN NSTEP 6 THEN NSTEP 7 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[
    MATCH_MP DISPATCH4_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 4)`));
    MATCH_MP DISPATCH_SMALL_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `5 <= nb`));
    COND_CLAUSES]) THEN
  MAP_EVERY NSTEP (8--36) THEN
  MAP_EVERY NSTEP (37--(setup_tail_branch-1)) THEN NSTEP setup_tail_branch THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SETUP_BRANCH_COND_FALSE_GEN
    (CONJ (ASSUME `8 * (k + 1) < nb`) (CONJ (ASSUME `nb <= 8 * (k + 2)`)
          (ASSUME `val (in_p:int64) + 128 * (k + 1) < 2 EXP 63`))); COND_CLAUSES]) THEN
  SETUP_LOADS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SETUP_BRANCH_COND_TRUE_2
    (CONJ (ASSUME `k = 0`) (CONJ (ASSUME `8 * (k + 1) < nb`)
      (CONJ (ASSUME `nb <= 8 * (k + 2)`)
          (ASSUME `val (in_p:int64) + 128 * (k + 1) < 2 EXP 63`))));
    COND_CLAUSES]) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY SETUP_RECON_TAC_GEN THEN
  DISCHARGE_SAFETY_PROPERTY_TAC)
;;

(* --- PREPRETAIL_TAIL_SAFE (pc+0xa10 -> pc+0x1154): the reusable last-group *)
(* + tail composite (PREPRETAIL_GEN_SAFE o TAIL_REM_SAFE, g = k+1,           *)
(* r = nb-8*(k+1)) for general k.  Double abstract bigstep; f_events takes   *)
(* nb and k.                                                                 *)
let AES_GCM_ENC_ALT_PREPRETAIL_TAIL_SAFE = prove
 (kterm `exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p mod_p end_p nb k pc.
    8 * (k + 1) <= nb /\
    8 * (k + 1) < nb /\ nb <= 8 * (k + 2) /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (key_p, keybytes); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + pc_prepretail) /\
           read X0 s = word_add in_p (word (128 * (k + 1))) /\
           read X2 s = word_add out_p (word (128 * (k + 1))) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read events s = e)
      (\s. read PC s = word (pc + pc_end) /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events in_p out_p tag_p ivec_p key_p htable_p mod_p nb k pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, keybytes;
                 htable_p, 192; mod_p, 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC AES_GCM_ENC_ALT_TAIL_REM_SAFE "H_TAIL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC AES_GCM_ENC_ALT_PREPRETAIL_GEN_SAFE "H_PP" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64)
      (key_p:int64) (htable_p:int64) (mod_p:int64) (nb:num) (k:num) (pc:num).
       APPEND
         (f_ev_tail in_p out_p tag_p ivec_p key_p htable_p mod_p nb k pc)
         (f_ev_pp in_p out_p tag_p ivec_p key_p htable_p mod_p nb k pc)
       :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
    MODIFIABLE_SIMD_REGS; MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS]) THEN
  (* ===== BIGSTEP 1: PREPRETAIL_GEN (pc+0xa10 -> pc+0xee0), e_tail = [] *)
  USE_THEN "H_PP" (fun th ->
    MP_TAC (REWRITE_RULE[APPEND]
      (SPECL [`e:(uarch_event)list`; `in_p:int64`; `out_p:int64`; `tag_p:int64`;
              `ivec_p:int64`; `key_p:int64`; `htable_p:int64`; `mod_p:int64`;
              `end_p:int64`; `nb:num`; `k:num`; `pc:num`;
              `[]:(uarch_event)list`] th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
    REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[] ORELSE
     CONV_TAC WORD_RULE);
    ALL_TAC] THEN
  ARM_BIGSTEP_TAC AES_GCM_ENC_ALT_EXEC "s1" THEN
  (* ===== BIGSTEP 2: TAIL_REM (pc+0xee0 -> pc+0x1154), g=k+1, r=nb-8*(k+1) *)
  USE_THEN "H_TAIL" (fun th ->
    MP_TAC (GEN_REWRITE_RULE I [RIGHT_FORALL_IMP_THM]
      (SPECL [`e:(uarch_event)list`; `in_p:int64`; `out_p:int64`; `tag_p:int64`;
              `ivec_p:int64`; `key_p:int64`; `htable_p:int64`; `mod_p:int64`;
              `end_p:int64`;
              `nb:num`; `nb - 8 * (k + 1)`; `k + 1`; `pc:num`] th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
    REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[] ORELSE
     CONV_TAC WORD_RULE);
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM LEFT_EXISTS_IMP_THM] THEN
  META_EXISTS_TAC THEN
  ARM_BIGSTEP_TAC AES_GCM_ENC_ALT_EXEC "s2" THENL [
    BINOP_TAC THENL [ UNIFY_REFL_TAC; REFL_TAC ] THEN NO_TAC;
    ALL_TAC ] THEN
  (* ===== CLOSE ===== *)
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
  CONJ_TAC THENL
   [ BINOP_TAC THENL [ UNIFY_F_EVENTS_TAC; UNIFY_F_EVENTS_TAC ];
     DISCHARGE_MEMACCESS_INBOUNDS_TAC ])
;;

(* --- Whole-core safety for nb 9..16: FIXED_CORRECT_G1_SAFE (pc+0x38 ->     *)
(* pc+0x1154, k = 0).  SETUP_G1_SAFE o PREPRETAIL_TAIL_SAFE (double          *)
(* bigstep).  f_events takes nb.                                             *)
let AES_GCM_ENC_ALT_FIXED_CORRECT_G1_SAFE = prove
 (kterm `exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p stackpointer len_bits end_p
     nb k pc.
    k = 0 /\
    8 * (k + 1) <= nb /\
    len_bits = 128 * nb /\
    8 * (k + 1) < nb /\ nb <= 8 * (k + 2) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (key_p, keybytes); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word len_bits /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (len_bits DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read events s = e)
      (\s. read PC s = word (pc + pc_end) /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events nb in_p out_p tag_p ivec_p key_p htable_p
                     stackpointer pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, keybytes;
                 htable_p, 192; word_add stackpointer (word 0x40), 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC AES_GCM_ENC_ALT_PREPRETAIL_TAIL_SAFE "H_PT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC AES_GCM_ENC_ALT_SETUP_G1_SAFE "H_SETUP" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(nb:num) (in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64)
      (key_p:int64) (htable_p:int64) (stackpointer:int64) (pc:num).
       APPEND
         (f_ev_pt nb in_p out_p tag_p ivec_p key_p htable_p stackpointer pc)
         (f_ev_setup nb in_p out_p tag_p ivec_p key_p htable_p stackpointer pc)
       :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
    MODIFIABLE_SIMD_REGS; MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS]) THEN
  (* ===== BIGSTEP 1: SETUP_G1 (pc+0x38 -> pc+0xa10), e_tail = [] ===== *)
  USE_THEN "H_SETUP" (fun th ->
    MP_TAC (REWRITE_RULE[APPEND]
      (SPECL [`e:(uarch_event)list`; `in_p:int64`; `out_p:int64`; `tag_p:int64`;
              `ivec_p:int64`; `key_p:int64`; `htable_p:int64`; `stackpointer:int64`;
              `len_bits:num`; `end_p:int64`; `nb:num`; `k:num`;
              `pc:num`; `[]:(uarch_event)list`] th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
    REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[] ORELSE
     CONV_TAC WORD_RULE);
    ALL_TAC] THEN
  ARM_BIGSTEP_TAC AES_GCM_ENC_ALT_EXEC "s1" THEN
  (* ===== BIGSTEP 2: PREPRETAIL_TAIL (pc+0xa10 -> pc+0x1154), k=0 ===== *)
  USE_THEN "H_PT" (fun th ->
    MP_TAC (GEN_REWRITE_RULE I [RIGHT_FORALL_IMP_THM]
      (SPECL [`e:(uarch_event)list`; `in_p:int64`; `out_p:int64`; `tag_p:int64`;
              `ivec_p:int64`; `key_p:int64`; `htable_p:int64`;
              `word_add stackpointer (word 0x40):int64`; `end_p:int64`;
              `nb:num`; `0`; `pc:num`] th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
    REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[] ORELSE
     CONV_TAC WORD_RULE);
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM LEFT_EXISTS_IMP_THM] THEN
  META_EXISTS_TAC THEN
  ARM_BIGSTEP_TAC AES_GCM_ENC_ALT_EXEC "s2" THENL [
    BINOP_TAC THENL [ UNIFY_REFL_TAC; REFL_TAC ] THEN NO_TAC;
    ALL_TAC ] THEN
  (* ===== CLOSE ===== *)
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
  CONJ_TAC THENL
   [ BINOP_TAC THENL [ UNIFY_F_EVENTS_TAC; UNIFY_F_EVENTS_TAC ];
     DISCHARGE_MEMACCESS_INBOUNDS_TAC ])
;;

(* --- SETUP_GEN_SAFE (pc+0x38 -> pc+0x4c0, k <> 0, nb >= 17): the setup for *)
(* the general (main-loop) case.  The same as SETUP_G1_SAFE except that the  *)
(* closing branch is SETUP_BRANCH_COND_FALSE_2_GEN (~(k = 0): fall into the  *)
(* main loop at pc+0x4c0 rather than skip to the prepretail).  The post is   *)
(* the MAIN_LOOP entry registers.                                            *)
let AES_GCM_ENC_ALT_SETUP_GEN_SAFE = prove
 (kterm `exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p stackpointer len_bits end_p
     nb k pc.
    ~(k = 0) /\
    8 * (k + 1) <= nb /\
    len_bits = 128 * nb /\
    8 * (k + 1) < nb /\ nb <= 8 * (k + 2) /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (key_p, keybytes); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word len_bits /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (len_bits DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read events s = e)
      (\s. read PC s = word (pc + pc_loop) /\
           read X0 s = word_add in_p (word (128 * (0 + 1))) /\
           read X2 s = word_add out_p (word (128 * (0 + 1))) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X11 s = key_p /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events in_p out_p tag_p ivec_p key_p htable_p
                     stackpointer pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, keybytes;
                 htable_p, 192; word_add stackpointer (word 0x40), 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64)
      (key_p:int64) (htable_p:int64) (stackpointer:int64) (pc:num).
       f_ev in_p out_p tag_p ivec_p key_p htable_p stackpointer pc
       :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN
   `?inblock. !j. j < nb
      ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s0 =
          inblock j`
   (CHOOSE_THEN ASSUME_TAC) THENL
   [EXISTS_TAC
      `\j. read (memory :> bytes128 (word_add in_p (word (16 * j)))) s0` THEN
    REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(nb = 4)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `5 <= nb` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY NSTEP (1--5) THEN NSTEP 6 THEN NSTEP 7 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[
    MATCH_MP DISPATCH4_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 4)`));
    MATCH_MP DISPATCH_SMALL_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `5 <= nb`));
    COND_CLAUSES]) THEN
  MAP_EVERY NSTEP (8--36) THEN
  MAP_EVERY NSTEP (37--(setup_tail_branch-1)) THEN NSTEP setup_tail_branch THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SETUP_BRANCH_COND_FALSE_GEN
    (CONJ (ASSUME `8 * (k + 1) < nb`) (CONJ (ASSUME `nb <= 8 * (k + 2)`)
          (ASSUME `val (in_p:int64) + 128 * (k + 1) < 2 EXP 63`))); COND_CLAUSES]) THEN
  SETUP_LOADS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SETUP_BRANCH_COND_FALSE_2_GEN
    (CONJ (ASSUME `~(k = 0)`) (CONJ (ASSUME `8 * (k + 1) < nb`)
      (CONJ (ASSUME `nb <= 8 * (k + 2)`)
          (ASSUME `val (in_p:int64) + 128 * (k + 1) < 2 EXP 63`))));
    COND_CLAUSES]) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY SETUP_RECON_TAC_GEN THEN
  DISCHARGE_SAFETY_PROPERTY_TAC)
;;

(* --- MAIN_LOOP_SAFE (pc+0x4c0 -> pc+0xa10, k iterations, nb >= 17): the    *)
(* 8-block main loop.  Lean invariant (pointer registers only);              *)
(* ENSURES_EVENTS_WHILE_UP2_TAC with pc2 = the exit (pc+0xa10).  The body is *)
(* the functional NSTEP_G drive, with the incremented ldps at steps          *)
(* 295/303/304 handled by LDP_STEP4_LEAN (LDP_STEP4_TAC without the          *)
(* INBLOCKS_TAC re-derivation, which safety does not need) and the b.lt at   *)
(* step 340; the back-edge PC is closed via BRIDGE_GE + IVAL_PTR_ADD (in_p   *)
(* cancels, leaving i+1 < k), the events via ENUMERATEL_ADD1.                *)
let LDP_STEP4_LEAN n =
  let sn = "s"^string_of_int n in
  ARM_VERBOSE_STEP_TAC AES_GCM_ENC_ALT_EXEC sn THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_add b (word m)) (word nn):int64 = word_add b (word(m+nn))`]) THEN
  RULE_ASSUM_TAC NORMOFF_RULE THEN
  RULE_ASSUM_TAC SUBWORD_NORM_RULE THEN
  DISCARD_OLDSTATE_TAC sn;;

let AES_GCM_ENC_ALT_MAIN_LOOP_SAFE = prove
 (kterm `exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p mod_p end_p nb k pc.
    ~(k = 0) /\
    8 * (k + 1) <= nb /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (key_p, keybytes); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + pc_loop) /\
           read X0 s = word_add in_p (word (128 * (0 + 1))) /\
           read X2 s = word_add out_p (word (128 * (0 + 1))) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read events s = e)
      (\s. read PC s = word (pc + pc_prepretail) /\
           read X0 s = word_add in_p (word (128 * (k + 1))) /\
           read X2 s = word_add out_p (word (128 * (k + 1))) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events in_p out_p tag_p ivec_p key_p htable_p mod_p nb k pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, keybytes;
                 htable_p, 192; mod_p, 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64)
      (key_p:int64) (htable_p:int64) (mod_p:int64) (nb:num) (k:num) (pc:num).
       APPEND
         (f_ev_post in_p out_p tag_p ivec_p key_p htable_p mod_p nb k pc)
         (APPEND
           (ENUMERATEL k
             (\i. f_ev_loop in_p out_p tag_p ivec_p key_p htable_p mod_p nb k pc i))
           (f_ev_pre in_p out_p tag_p ivec_p key_p htable_p mod_p nb k pc))
       :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `k:num`
    (kterm `pc + pc_loop`) (kterm `pc + pc_prepretail`)
    `\i s. read X0 s = word_add in_p (word (128 * (i + 1))) /\
           read X2 s = word_add out_p (word (128 * (i + 1))) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* init (0-step) *)
    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ENUMERATEL; APPEND] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    (* body *)
    ALL_TAC;
    (* exit (0-step, pc2 = post PC) *)
    ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[APPEND_NIL; APPEND] THEN DISCHARGE_SAFETY_PROPERTY_TAC] THEN
  (* ===== loop body: pc+0x4c0 .. b.lt at pc+0xa0c (340 steps) ===== *)
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES_GCM_ENC_ALT_EXEC]
    (kterm `LENGTH tmc`)]) THEN
  MAP_EVERY NSTEP_G (1--(loop_ldp1-1)) THEN
  LDP_STEP4_LEAN loop_ldp1 THEN
  MAP_EVERY NSTEP_G ((loop_ldp1+1)--(loop_ldp2-1)) THEN
  LDP_STEP4_LEAN loop_ldp2 THEN
  LDP_STEP4_LEAN (loop_ldp2+1) THEN
  MAP_EVERY NSTEP_G ((loop_ldp2+2)--loop_backedge) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (* PC branch: <b.lt cond> <=> i+1<k, via BRIDGE_GE + IVAL_PTR_ADD *)
  CONJ_TAC THENL
   [REWRITE_TAC[BRIDGE_GE] THEN
    SUBGOAL_THEN
      `ival(word_add in_p (word (128 * (k + 1)))) = &(val(in_p:int64) + 128 * (k + 1)) /\
       ival(word_add in_p (word (128 * (i + 1) + 128))) = &(val(in_p:int64) + (128 * (i + 1) + 128))`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THEN MATCH_MP_TAC IVAL_PTR_ADD THEN
      UNDISCH_TAC `val(in_p:int64) + 128 * (k + 1) < 2 EXP 63` THEN
      UNDISCH_TAC `(i:num) < k` THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[INT_OF_NUM_LE] THEN
    GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN
    MATCH_MP_TAC (MESON[]
      `(p <=> q) ==> ((if p then (a:int64) else b) = (if q then a else b))`) THEN
    UNDISCH_TAC `(i:num) < k` THEN ARITH_TAC;
    ALL_TAC] THEN
  (* X0, X2 pointer advances *)
  CONJ_TAC THENL [ AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC ] THEN
  CONJ_TAC THENL [ AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC ] THEN
  (* events: e2 = ENUMERATEL (i+1) e_loop; unify f_ev_loop i := this         *)
  (* iteration's trace                                                       *)
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
  CONJ_TAC THENL
   [PURE_REWRITE_TAC[APPEND_NIL] THEN
    GEN_REWRITE_TAC RAND_CONV [ENUMERATEL_ADD1] THEN
    BETA_TAC THEN
    BINOP_TAC THENL [ UNIFY_F_EVENTS_TAC; REFL_TAC ];
    DISCHARGE_MEMACCESS_INBOUNDS_TAC])
;;

(* --- LOOP_TAIL_SAFE (pc+0x4c0 -> pc+0x1154): MAIN_LOOP_SAFE o              *)
(* PREPRETAIL_TAIL_SAFE (double abstract bigstep, parameter k), the loop +   *)
(* prepretail + tail composite for nb >= 17.                                 *)
let AES_GCM_ENC_ALT_LOOP_TAIL_SAFE = prove
 (kterm `exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p mod_p end_p nb k pc.
    ~(k = 0) /\
    8 * (k + 1) <= nb /\
    8 * (k + 1) < nb /\ nb <= 8 * (k + 2) /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (key_p, keybytes); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + pc_loop) /\
           read X0 s = word_add in_p (word (128 * (0 + 1))) /\
           read X2 s = word_add out_p (word (128 * (0 + 1))) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read events s = e)
      (\s. read PC s = word (pc + pc_end) /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events in_p out_p tag_p ivec_p key_p htable_p mod_p nb k pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, keybytes;
                 htable_p, 192; mod_p, 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC AES_GCM_ENC_ALT_PREPRETAIL_TAIL_SAFE "H_PT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC AES_GCM_ENC_ALT_MAIN_LOOP_SAFE "H_ML" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64)
      (key_p:int64) (htable_p:int64) (mod_p:int64) (nb:num) (k:num) (pc:num).
       APPEND
         (f_ev_pt in_p out_p tag_p ivec_p key_p htable_p mod_p nb k pc)
         (f_ev_ml in_p out_p tag_p ivec_p key_p htable_p mod_p nb k pc)
       :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
    MODIFIABLE_SIMD_REGS; MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS]) THEN
  (* ===== BIGSTEP 1: MAIN_LOOP (pc+0x4c0 -> pc+0xa10), e_tail = [] ===== *)
  USE_THEN "H_ML" (fun th ->
    MP_TAC (REWRITE_RULE[APPEND]
      (SPECL [`e:(uarch_event)list`; `in_p:int64`; `out_p:int64`; `tag_p:int64`;
              `ivec_p:int64`; `key_p:int64`; `htable_p:int64`; `mod_p:int64`;
              `end_p:int64`; `nb:num`; `k:num`; `pc:num`;
              `[]:(uarch_event)list`] th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
    REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[] ORELSE
     CONV_TAC WORD_RULE);
    ALL_TAC] THEN
  ARM_BIGSTEP_TAC AES_GCM_ENC_ALT_EXEC "s1" THEN
  (* ===== BIGSTEP 2: PREPRETAIL_TAIL (pc+0xa10 -> pc+0x1154), param k ===== *)
  USE_THEN "H_PT" (fun th ->
    MP_TAC (GEN_REWRITE_RULE I [RIGHT_FORALL_IMP_THM]
      (SPECL [`e:(uarch_event)list`; `in_p:int64`; `out_p:int64`; `tag_p:int64`;
              `ivec_p:int64`; `key_p:int64`; `htable_p:int64`; `mod_p:int64`;
              `end_p:int64`; `nb:num`; `k:num`; `pc:num`] th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
    REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[] ORELSE
     CONV_TAC WORD_RULE);
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM LEFT_EXISTS_IMP_THM] THEN
  META_EXISTS_TAC THEN
  ARM_BIGSTEP_TAC AES_GCM_ENC_ALT_EXEC "s2" THENL [
    BINOP_TAC THENL [ UNIFY_REFL_TAC; REFL_TAC ] THEN NO_TAC;
    ALL_TAC ] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
  CONJ_TAC THENL
   [ BINOP_TAC THENL [ UNIFY_F_EVENTS_TAC; UNIFY_F_EVENTS_TAC ];
     DISCHARGE_MEMACCESS_INBOUNDS_TAC ])
;;

(* --- Whole-core safety for nb >= 17: GEN_CORRECT_SAFE (pc+0x38 ->          *)
(* pc+0x1154, k >= 1).  SETUP_GEN_SAFE o LOOP_TAIL_SAFE (double bigstep).    *)
(* f_events takes nb and k.                                                  *)
let AES_GCM_ENC_ALT_GEN_CORRECT_SAFE = prove
 (kterm `exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p stackpointer len_bits end_p
     nb k pc.
    ~(k = 0) /\
    8 * (k + 1) <= nb /\
    len_bits = 128 * nb /\
    8 * (k + 1) < nb /\ nb <= 8 * (k + 2) /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (key_p, keybytes); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word len_bits /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (len_bits DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read events s = e)
      (\s. read PC s = word (pc + pc_end) /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events nb k in_p out_p tag_p ivec_p key_p htable_p
                     stackpointer pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, keybytes;
                 htable_p, 192; word_add stackpointer (word 0x40), 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC AES_GCM_ENC_ALT_LOOP_TAIL_SAFE "H_LT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC AES_GCM_ENC_ALT_SETUP_GEN_SAFE "H_SG" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(nb:num) (k:num) (in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64)
      (key_p:int64) (htable_p:int64) (stackpointer:int64) (pc:num).
       APPEND
         (f_ev_lt nb k in_p out_p tag_p ivec_p key_p htable_p stackpointer pc)
         (f_ev_sg nb k in_p out_p tag_p ivec_p key_p htable_p stackpointer pc)
       :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
    MODIFIABLE_SIMD_REGS; MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS]) THEN
  (* ===== BIGSTEP 1: SETUP_GEN (pc+0x38 -> pc+0x4c0), e_tail = [] ===== *)
  USE_THEN "H_SG" (fun th ->
    MP_TAC (REWRITE_RULE[APPEND]
      (SPECL [`e:(uarch_event)list`; `in_p:int64`; `out_p:int64`; `tag_p:int64`;
              `ivec_p:int64`; `key_p:int64`; `htable_p:int64`; `stackpointer:int64`;
              `len_bits:num`; `end_p:int64`; `nb:num`; `k:num`;
              `pc:num`; `[]:(uarch_event)list`] th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
    REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[] ORELSE
     CONV_TAC WORD_RULE);
    ALL_TAC] THEN
  ARM_BIGSTEP_TAC AES_GCM_ENC_ALT_EXEC "s1" THEN
  (* ===== BIGSTEP 2: LOOP_TAIL (pc+0x4c0 -> pc+0x1154), param k ===== *)
  USE_THEN "H_LT" (fun th ->
    MP_TAC (GEN_REWRITE_RULE I [RIGHT_FORALL_IMP_THM]
      (SPECL [`e:(uarch_event)list`; `in_p:int64`; `out_p:int64`; `tag_p:int64`;
              `ivec_p:int64`; `key_p:int64`; `htable_p:int64`;
              `word_add stackpointer (word 0x40):int64`; `end_p:int64`;
              `nb:num`; `k:num`; `pc:num`] th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
    REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[] ORELSE
     CONV_TAC WORD_RULE);
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM LEFT_EXISTS_IMP_THM] THEN
  META_EXISTS_TAC THEN
  ARM_BIGSTEP_TAC AES_GCM_ENC_ALT_EXEC "s2" THENL [
    BINOP_TAC THENL [ UNIFY_REFL_TAC; REFL_TAC ] THEN NO_TAC;
    ALL_TAC ] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
  CONJ_TAC THENL
   [ BINOP_TAC THENL [ UNIFY_F_EVENTS_TAC; UNIFY_F_EVENTS_TAC ];
     DISCHARGE_MEMACCESS_INBOUNDS_TAC ])
;;

(* --- Whole-core safety (all nb): a dispatch over the four nb ranges        *)
(* (nb <= 4: FAST1..FAST4; 5..8: SETUP0_TAIL; 9..16: FIXED_CORRECT_G1;       *)
(* >= 17: GEN_CORRECT), following AES_GCM_ENC_ALT_CORRECT's case tree.       *)
(* Entry pc+0x38, exit pc+0x1154.                                            *)
let AES_GCM_ENC_ALT_SAFE = prove
 (kterm `exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p stackpointer len_bits
     nb pc.
    1 <= nb /\
    len_bits = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH tmc);
       (in_p, 16 * nb); (key_p, keybytes); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word len_bits /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (len_bits DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read events s = e)
      (\s. read PC s = word (pc + pc_end) /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events nb in_p out_p tag_p ivec_p key_p htable_p
                     stackpointer pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, keybytes;
                 htable_p, 192; word_add stackpointer (word 0x40), 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  X_CHOOSE_TAC `w1:int64->int64->int64->int64->int64->int64->int64->num->(uarch_event)list` AES_GCM_ENC_ALT_FAST1_SAFE THEN
  X_CHOOSE_TAC `w2:int64->int64->int64->int64->int64->int64->int64->num->(uarch_event)list` AES_GCM_ENC_ALT_FAST2_SAFE THEN
  X_CHOOSE_TAC `w3:int64->int64->int64->int64->int64->int64->int64->num->(uarch_event)list` AES_GCM_ENC_ALT_FAST3_SAFE THEN
  X_CHOOSE_TAC `w4:int64->int64->int64->int64->int64->int64->int64->num->(uarch_event)list` AES_GCM_ENC_ALT_FAST4_SAFE THEN
  X_CHOOSE_TAC `wst:num->int64->int64->int64->int64->int64->int64->int64->num->(uarch_event)list` AES_GCM_ENC_ALT_SETUP0_TAIL_SAFE THEN
  X_CHOOSE_TAC `wg1:num->int64->int64->int64->int64->int64->int64->int64->num->(uarch_event)list` AES_GCM_ENC_ALT_FIXED_CORRECT_G1_SAFE THEN
  X_CHOOSE_TAC `wgen:num->num->int64->int64->int64->int64->int64->int64->int64->num->(uarch_event)list` AES_GCM_ENC_ALT_GEN_CORRECT_SAFE THEN
  EXISTS_TAC
   `\(nb:num) (in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64)
     (key_p:int64) (htable_p:int64) (stackpointer:int64) (pc:num).
      if nb = 1 then w1 in_p out_p tag_p ivec_p key_p htable_p stackpointer pc
      else if nb = 2 then w2 in_p out_p tag_p ivec_p key_p htable_p stackpointer pc
      else if nb = 3 then w3 in_p out_p tag_p ivec_p key_p htable_p stackpointer pc
      else if nb = 4 then w4 in_p out_p tag_p ivec_p key_p htable_p stackpointer pc
      else if nb <= 8 then wst nb in_p out_p tag_p ivec_p key_p htable_p stackpointer pc
      else if nb <= 16 then wg1 nb in_p out_p tag_p ivec_p key_p htable_p stackpointer pc
      else wgen nb ((nb - 1) DIV 8 - 1) in_p out_p tag_p ivec_p key_p htable_p stackpointer pc
      :(uarch_event)list` THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `in_p:int64`; `out_p:int64`; `tag_p:int64`;
    `ivec_p:int64`; `key_p:int64`; `htable_p:int64`; `stackpointer:int64`;
    `len_bits:num`; `nb:num`; `pc:num`] THEN
  STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `nb <= 8 \/ (9 <= nb /\ nb <= 16) \/ 17 <= nb` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THENL
   [ASM_CASES_TAC `nb = 1` THENL
     [REWRITE_TAC[EQT_INTRO(ASSUME `nb = 1`); COND_CLAUSES] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
     (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE (REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN ASM_REWRITE_TAC[]) ORELSE CONV_TAC WORD_RULE);
      ALL_TAC] THEN
    ASM_CASES_TAC `nb = 2` THENL
     [REWRITE_TAC[EQF_INTRO(ASSUME `~(nb = 1)`); EQT_INTRO(ASSUME `nb = 2`); COND_CLAUSES] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
     (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE (REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN ASM_REWRITE_TAC[]) ORELSE CONV_TAC WORD_RULE);
      ALL_TAC] THEN
    ASM_CASES_TAC `nb = 3` THENL
     [REWRITE_TAC[EQF_INTRO(ASSUME `~(nb = 1)`); EQF_INTRO(ASSUME `~(nb = 2)`); EQT_INTRO(ASSUME `nb = 3`); COND_CLAUSES] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
     (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE (REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN ASM_REWRITE_TAC[]) ORELSE CONV_TAC WORD_RULE);
      ALL_TAC] THEN
    ASM_CASES_TAC `nb = 4` THENL
     [REWRITE_TAC[EQF_INTRO(ASSUME `~(nb = 1)`); EQF_INTRO(ASSUME `~(nb = 2)`); EQF_INTRO(ASSUME `~(nb = 3)`); EQT_INTRO(ASSUME `nb = 4`); COND_CLAUSES] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
     (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE (REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN ASM_REWRITE_TAC[]) ORELSE CONV_TAC WORD_RULE);
      ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 1) /\ ~(nb = 2) /\ ~(nb = 3) /\ ~(nb = 4)` STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[EQF_INTRO(ASSUME `~(nb = 1)`); EQF_INTRO(ASSUME `~(nb = 2)`); EQF_INTRO(ASSUME `~(nb = 3)`); EQF_INTRO(ASSUME `~(nb = 4)`); EQT_INTRO(ASSUME `nb <= 8`); COND_CLAUSES] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE (REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN ASM_REWRITE_TAC[]) ORELSE CONV_TAC WORD_RULE);
    SUBGOAL_THEN `~(nb = 1) /\ ~(nb = 2) /\ ~(nb = 3) /\ ~(nb = 4) /\ ~(nb <= 8)` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EQF_INTRO(ASSUME `~(nb = 1)`); EQF_INTRO(ASSUME `~(nb = 2)`); EQF_INTRO(ASSUME `~(nb = 3)`); EQF_INTRO(ASSUME `~(nb = 4)`); EQF_INTRO(ASSUME `~(nb <= 8)`); EQT_INTRO(ASSUME `nb <= 16`); COND_CLAUSES] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `word_add in_p (word (128 * (0 + 1))):int64` THEN EXISTS_TAC `0` THEN
    REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE (REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN ASM_REWRITE_TAC[]) ORELSE CONV_TAC WORD_RULE);
    SUBGOAL_THEN `~(nb = 1) /\ ~(nb = 2) /\ ~(nb = 3) /\ ~(nb = 4) /\ ~(nb <= 8) /\ ~(nb <= 16)` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EQF_INTRO(ASSUME `~(nb = 1)`); EQF_INTRO(ASSUME `~(nb = 2)`); EQF_INTRO(ASSUME `~(nb = 3)`); EQF_INTRO(ASSUME `~(nb = 4)`); EQF_INTRO(ASSUME `~(nb <= 8)`); EQF_INTRO(ASSUME `~(nb <= 16)`); COND_CLAUSES] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `word_add in_p (word (128 * (((nb - 1) DIV 8 - 1) + 1))):int64` THEN
    MP_TAC(SPECL [`nb - 1`; `8`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
    ABBREV_TAC `q = (nb - 1) DIV 8` THEN ABBREV_TAC `r = (nb - 1) MOD 8` THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE (REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN ASM_REWRITE_TAC[]) ORELSE CONV_TAC WORD_RULE)])
;;

(* The two exported safety statements below are the terms mk_safety_spec     *)
(* generates from the correctness theorems and the C signature, pinned with  *)
(* ASSERT_CONCL_TAC so that the load fails unless the written statement is   *)
(* exactly the generated one.  The bounds size in/out from len_bits/8, then  *)
(* tag 16, ivec 16, key keybytes, htable 24*8 = 192 and the 80-byte frame;   *)
(* apart from the loaded code they constrain no memory contents.             *)
(* ~keep_maychanges keeps the correctness theorem's MAYCHANGE frame.         *)
let enc_safety_full_spec_tmc,enc_safety_public_vars_tmc = mk_safety_spec
    ~keep_maychanges:true
    (assoc aes_gcm_enc_alt_name subroutine_signatures)
    AES_GCM_ENC_ALT_NOIBT_SUBROUTINE_CORRECT
    AES_GCM_ENC_ALT_EXEC;;

(* --- NOIBT subroutine safety: the 3-path wrapper corresponding to          *)
(* AES_GCM_ENC_ALT_NOIBT_SUBROUTINE_CORRECT.  f_events dispatches on the     *)
(* public length guards (misaligned / zero / main); the main path is the     *)
(* prologue, a callee bigstep with AES_GCM_ENC_ALT_SAFE (assumed as          *)
(* H_CORE; in-frame SP = word_sub sp 0x50) and the epilogue.  The statement  *)
(* is the mk_safety_spec-generated enc_safety_full_spec_tmc.                 *)
let AES_GCM_ENC_ALT_NOIBT_SUBROUTINE_SAFE = prove
 (kterm `exists f_events.
    forall e in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        val in_p + 16 * gcm_wb_blocks len_bits < 2 EXP 63 /\
        ALLPAIRS nonoverlapping
        [out_p,16 * gcm_wb_blocks len_bits; tag_p,16; ivec_p,16;
         word_sub stackpointer (word 80),80]
        [word pc,LENGTH tmc;
         in_p,16 * gcm_wb_blocks len_bits; key_p,keybytes; htable_p,192] /\
        PAIRWISE nonoverlapping
        [out_p,16 * gcm_wb_blocks len_bits; tag_p,16; ivec_p,16;
         word_sub stackpointer (word 80),80]
        ==> ensures arm
            (\s.
                 aligned_bytes_loaded s (word pc) tmc /\
                 read PC s = word pc /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS
                 [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p]
                 s /\
                 read events s = e)
            (\s.
                 read PC s = returnaddress /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 =
                      f_events in_p key_p htable_p out_p tag_p ivec_p
                      len_bits
                      pc
                      (word_sub stackpointer (word 80))
                      returnaddress /\
                      memaccess_inbounds e2
                      [in_p,val len_bits DIV 8 * 1; tag_p,16; ivec_p,16;
                       key_p,keybytes; htable_p,192;
                       out_p,val len_bits DIV 8 * 1;
                       word_sub stackpointer (word 80),80]
                      [out_p,val len_bits DIV 8 * 1; tag_p,16; ivec_p,16;
                       word_sub stackpointer (word 80),80]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
             [memory :> bytes (out_p,16 * gcm_wb_blocks len_bits);
              memory :> bytes (tag_p,16); memory :> bytes (ivec_p,16);
              memory :> bytes (word_sub stackpointer (word 80),80)])`,
  ASSERT_CONCL_TAC enc_safety_full_spec_tmc THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC AES_GCM_ENC_ALT_SAFE "H_CORE" THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; LENGTH_WB_MC; ALLPAIRS;
              PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS; KEY_SPLIT] THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(in_p:int64) (key_p:int64) (htable_p:int64) (out_p:int64) (tag_p:int64)
      (ivec_p:int64) (len_bits:int64) (pc:num) (sp:int64) (retaddr:int64).
      if val len_bits MOD 128 = 0 then
        (if val len_bits = 0 then
           f_ev_zero len_bits in_p out_p tag_p ivec_p key_p htable_p pc sp retaddr
         else
           APPEND
             (f_ev_epi in_p out_p tag_p ivec_p key_p htable_p pc sp retaddr)
             (APPEND
               (f_ev_core (gcm_wb_blocks len_bits) in_p out_p tag_p ivec_p key_p htable_p sp pc)
               (f_ev_pro in_p out_p tag_p ivec_p key_p htable_p pc sp retaddr)))
       else
         f_ev_mis len_bits in_p out_p tag_p ivec_p key_p htable_p pc sp retaddr
      :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `nb = gcm_wb_blocks len_bits` THEN
  ASM_CASES_TAC `val(len_bits:int64) MOD 128 = 0` THENL
   [ALL_TAC;
    (* ===== Path 3: misaligned length ===== *)
    SUBGOAL_THEN `nb = 0` SUBST_ALL_TAC THENL
     [EXPAND_TAC "nb" THEN REWRITE_TAC[gcm_wb_blocks] THEN ASM_REWRITE_TAC[COND_CLAUSES]; ALL_TAC] THEN
    SUBGOAL_THEN `~(val(len_bits:int64) = 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~(val(len_bits:int64) MOD 128 = 0)` THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    SUBGOAL_THEN `~(len_bits:int64 = word 0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[GSYM VAL_EQ_0]; ALL_TAC] THEN
    SUBGOAL_THEN `~(word_and (len_bits:int64) (word 0x7f) = word 0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[WB_MASK7_EQ_MOD]; ALL_TAC] THEN
    SUBGOAL_THEN `~(val(word_and (len_bits:int64) (word 0x7f)) = 0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[VAL_EQ_0]; ALL_TAC] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC AES_GCM_ENC_ALT_EXEC [1] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(val(len_bits:int64) = 0)`;
                               ASSUME `~(len_bits:int64 = word 0)`; COND_CLAUSES]) THEN
    ARM_STEPS_TAC AES_GCM_ENC_ALT_EXEC [2] THEN
    ARM_STEPS_TAC AES_GCM_ENC_ALT_EXEC [3] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[
      ASSUME `~(word_and (len_bits:int64) (word 0x7f) = word 0)`;
      ASSUME `~(val(word_and (len_bits:int64) (word 0x7f)) = 0)`; COND_CLAUSES]) THEN
    ARM_STEPS_TAC AES_GCM_ENC_ALT_EXEC [4;5] THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[COND_CLAUSES] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN
  ASM_CASES_TAC `val(len_bits:int64) = 0` THENL
   [(* ===== Path 1: zero length ===== *)
    SUBGOAL_THEN `nb = 0` SUBST_ALL_TAC THENL
     [EXPAND_TAC "nb" THEN REWRITE_TAC[gcm_wb_blocks] THEN
      ASM_REWRITE_TAC[COND_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    SUBGOAL_THEN `len_bits:int64 = word 0` SUBST_ALL_TAC THENL
     [ASM_REWRITE_TAC[GSYM VAL_EQ_0]; ALL_TAC] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC AES_GCM_ENC_ALT_EXEC [1;2;3] THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[VAL_WORD_0; COND_CLAUSES] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  (* ===== Path 2: main (nonzero whole blocks) ===== *)
  SUBGOAL_THEN `1 <= nb` ASSUME_TAC THENL
   [EXPAND_TAC "nb" THEN REWRITE_TAC[gcm_wb_blocks] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`val(len_bits:int64)`; `128`] (CONJUNCT2 DIVISION_SIMP)) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(len_bits:int64) = 128 * nb` ASSUME_TAC THENL
   [EXPAND_TAC "nb" THEN ASM_SIMP_TAC[GCM_WB_BLOCKS_VALID]; ALL_TAC] THEN
  SUBGOAL_THEN `128 * nb < 2 EXP 64` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MP_TAC(ISPEC `len_bits:int64` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word(128 * nb):int64) = 128 * nb` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `gcm_wb_blocks(word(128 * nb):int64) = nb` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[gcm_wb_blocks] THEN
    SIMP_TAC[DIV_MULT; MOD_MULT; ARITH_EQ] THEN REWRITE_TAC[COND_CLAUSES]; ALL_TAC] THEN
  SUBGOAL_THEN `len_bits:int64 = word (128 * nb)` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(fun th -> if concl th = `val(len_bits:int64) = 128 * nb`
      then MP_TAC th else failwith "") THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[WORD_VAL]; ALL_TAC] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun c -> ENSURES_PRESERVED_DREG_TAC ("init_"^fst(dest_const c)) c)
    [`D8`;`D9`;`D10`;`D11`;`D12`;`D13`;`D14`;`D15`] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(
    EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV THENC REWRITE_CONV[WORD_ADD_0]))) THEN
  ARM_STEPS_TAC AES_GCM_ENC_ALT_EXEC [1] THEN
  SUBGOAL_THEN `~(128 * nb = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `1 <= nb` THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP WB_GUARD1_NONZERO_GEN
    (CONJ (ASSUME `1 <= nb`) (ASSUME `128 * nb < 2 EXP 64`));
    ASSUME `~(128 * nb = 0)`; COND_CLAUSES]) THEN
  ARM_STEPS_TAC AES_GCM_ENC_ALT_EXEC [2] THEN
  ARM_STEPS_TAC AES_GCM_ENC_ALT_EXEC [3] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP WB_GUARD2_MASK_GEN
    (CONJ (ASSUME `1 <= nb`) (ASSUME `128 * nb < 2 EXP 64`));
    VAL_WORD_0; COND_CLAUSES]) THEN
  ARM_STEPS_TAC AES_GCM_ENC_ALT_EXEC (4--14) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP WB_X9_NORM (ASSUME `128 * nb < 2 EXP 64`)]) THEN
  USE_THEN "H_CORE" (fun th0 ->
    let th = REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
               MODIFIABLE_SIMD_REGS; MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] th0 in
    MP_TAC (GEN_REWRITE_RULE I [RIGHT_FORALL_IMP_THM]
      (SPECL [`e:(uarch_event)list`; `in_p:int64`; `out_p:int64`; `tag_p:int64`;
              `ivec_p:int64`; `key_p:int64`; `htable_p:int64`;
              `word_sub stackpointer (word 80):int64`; `128 * nb`;
              `nb:num`; `pc:num`] th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
    REPEAT CONJ_TAC THEN
    (NONOVERLAPPING_TAC ORELSE ASM_ARITH_TAC ORELSE CONV_TAC WORD_RULE ORELSE
     ASM_REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS]); ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM LEFT_EXISTS_IMP_THM] THEN
  META_EXISTS_TAC THEN
  ARM_BIGSTEP_TAC AES_GCM_ENC_ALT_EXEC "s15" THENL
   [ CONV_TAC(LAND_CONV CONS_TO_APPEND_CONV) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
     UNIFY_REFL_TAC; ALL_TAC ] THEN
  ARM_STEPS_TAC AES_GCM_ENC_ALT_EXEC (16--22) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[COND_CLAUSES] THEN
  ABBREV_TAC `spoff:int64 = word_sub stackpointer (word 80)` THEN
  CONJ_TAC THENL [
    SAFE_META_EXISTS_TAC allowed_vars_e THEN
    CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
    CONJ_TAC THENL [
      REWRITE_TAC[APPEND_NIL] THEN
      BINOP_TAC THENL [
        UNIFY_F_EVENTS_TAC;
        BINOP_TAC THENL [
          ASM_REWRITE_TAC[] THEN UNIFY_F_EVENTS_TAC;
          UNIFY_F_EVENTS_TAC ] ];
      DISCHARGE_MEMACCESS_INBOUNDS_TAC ];
    EXPAND_TAC "spoff" THEN
    SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_128; LE_REFL; ARITH] THEN
    REPEAT CONJ_TAC THEN CONV_TAC WORD_RULE ]
);;

the_implicit_types := enc_alt_saved_implicit_types;;
