(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Region lemmas for mldsa87_verify_internal that the other parameter sets   *)
(* do not need. The code computes c2 = H(mu, w1') by a call of mld_H, which  *)
(* clang keeps in 44 and 65 but inlines in 87 (C2): the 64 bytes of mu (at   *)
(* rsp0 + 1408) and the 1024 bytes of w1' (at rsp0 + 3584) are absorbed into *)
(* the Keccak state at rsp0 + 32 as 8 full blocks of 136 bytes (the first    *)
(* from mu and the first 72 bytes of w1', the others by a loop with R14 the  *)
(* pointer into w1'), then the padding and the last permutation. The loop    *)
(* runs 7 times for this length, so the lemma steps through it as straight-  *)
(* line code, as TRG does for tr (inline_verify65.ml), whose block tactics   *)
(* it shares: the message is M = MU + 2^512 W1, and the chunks of the block  *)
(* k are read from w1' at the offsets 72 + 136 (k - 1) + 16 j. CMP87 is the  *)
(* comparison of the 64 bytes of c~ with c2.                                 *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_verify65.ml";;

(*** Chunks of MU and W1 as chunks of M = MU + 2^512 * W1 ***)

let C2_MU_CHUNK = prove
 (`!MU W1 p n. MU < 2 EXP 512 /\ p + n <= 512
       ==> (MU DIV 2 EXP p) MOD 2 EXP n =
           ((MU + 2 EXP 512 * W1) DIV 2 EXP p) MOD 2 EXP n`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[DIV_MOD; MULT_EQ_0; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `2 EXP 512 = 2 EXP (512 - (p + n)) * 2 EXP (p + n)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `MU + (2 EXP (512 - (p + n)) * 2 EXP (p + n)) * W1 =
                (2 EXP (512 - (p + n)) * W1) * 2 EXP (p + n) + MU` SUBST1_TAC THENL
   [MESON_TAC[MULT_AC; ADD_AC]; REWRITE_TAC[MOD_MULT_ADD]]);;

let C2_W1_CHUNK = prove
 (`!MU W1 p n. MU < 2 EXP 512
       ==> (W1 DIV 2 EXP p) MOD 2 EXP n =
           ((MU + 2 EXP 512 * W1) DIV 2 EXP (512 + p)) MOD 2 EXP n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
  SUBGOAL_THEN `(MU + 2 EXP 512 * W1) DIV 2 EXP 512 = W1` (fun th -> REWRITE_TAC[th]) THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
  ASM_SIMP_TAC[DIV_LT; ADD_CLAUSES]);;

(*** The facts for the loads of chunk j (128 or 64 bits, at bit position ***)
(*** pos of block k of M = PK) read at byte off of mu or of w1'          ***)

let C2_SRC_TAC (k:int) (bits:int) (pos:int) (src:term) (len:int) (off:int) =
  let pat = subst [src,`a:int64`; mk_small_numeral len,`n:num`]
              `read (memory :> bytes(a,n)) (s:x86state)` in
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && can (term_match [] pat) (lhs c) then
      let s = rand(lhs c) and x = rhs c in
      let lem = if bits = 128 then TR_CHUNK128_OF_NUM else TR_CHUNK64_OF_NUM in
      let th1 = TR_NORM_RULE(tr_mp_conj
                  (SPECL [src; mk_small_numeral len; x; mk_small_numeral off; s] lem) th) in
      let eq0 =
        if len = 64 then
          MP (SPECL [`MU:num`; `W1:num`; mk_small_numeral (8 * off); mk_small_numeral bits]
                    C2_MU_CHUNK)
             (CONJ (ASSUME `MU < 2 EXP 512`)
                   (tr_num_true(mk_binop `(<=):num->num->bool`
                     (mk_binop `(+):num->num->num` (mk_small_numeral (8 * off)) (mk_small_numeral bits))
                     `512`)))
        else MP (SPECL [`MU:num`; `W1:num`; mk_small_numeral (8 * off); mk_small_numeral bits]
                       C2_W1_CHUNK) (ASSUME `MU < 2 EXP 512`) in
      let eq = CONV_RULE(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV) THENC
                         REWRITE_CONV[CONJUNCT1 EXP; DIV_1; ASSUME `MU + 2 EXP 512 * W1 = PK`]) eq0 in
      let ty = if bits = 128 then `:128` else `:64` in
      let th2 = TR_NORM_RULE(tr_mp_num (INST_TYPE [ty,`:N`]
                  (SPECL [`PK:num`; mk_small_numeral k; mk_small_numeral pos;
                          mk_small_numeral bits] TR_BLK_SUB))) in
      let th3 = TRANS (CONV_RULE(RAND_CONV(REWRITE_CONV[eq])) th1) (SYM th2) in
      ASSUME_TAC th3
    else NO_TAC);;

(*** The state after the padding of a full message (byte 0 and byte 135) ***)

let TR_PAD0_MERGE = prove
 (`!(a:int64) (S:1600 word) (s:x86state).
  read (memory :> bytes8 a) s = word_xor (word_subword S (0,8)) (word 31) /\
  (!m. m < 7 ==> read (memory :> bytes8 (word_add a (word (1 + m)))) s =
                 word_subword S (8 + 8 * m,8)) /\
  (!n. n < 15 ==> read (memory :> bytes64 (word_add a (word (8 + 8 * n)))) s =
                  word_subword S (64 + 64 * n,64)) /\
  (!m. m < 7 ==> read (memory :> bytes8 (word_add a (word (128 + m)))) s =
                 word_subword S (1024 + 8 * m,8)) /\
  read (memory :> bytes8 (word_add a (word 135))) s =
  word_xor (word_subword S (1080,8)) (word 128) /\
  (!n. n < 8 ==> read (memory :> bytes64 (word_add a (word (136 + 8 * n)))) s =
                 word_subword S (1088 + 64 * n,64))
  ==> read (memory :> wbytes a) s =
      word_xor (word_xor S (word(2 EXP 0 * 31))) (word(2 EXP 1080 * 128))`,
  REPEAT GEN_TAC THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV EXPAND_CASES_CONV)) THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV) THENC
                     REWRITE_CONV[WORD_ADD_0])) THEN
  STRIP_TAC THEN
  MP_TAC(CONV_RULE(RAND_CONV(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV))
      (READ_MEMORY_MERGE_CONV 3 `read (memory :> bytes64 (a:int64)) (s:x86state)`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC READ_MEMORY_WBYTES_OF_LANES THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN
  GEN_REWRITE_TAC (ONCE_DEPTH_CONV o LAND_CONV)
   [CONV_RULE(RAND_CONV(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV))
      (READ_MEMORY_MERGE_CONV 3
        `read (memory :> bytes64 (word_add (a:int64) (word 128))) (s:x86state)`)] THEN
  ASM_REWRITE_TAC[WORD_SUBWORD_XOR; WORD_XOR_0] THEN
  CONV_TAC(NUM_REDUCE_CONV THENC WORD_REDUCE_CONV) THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

(*** mld_shake256_state of 1088 bytes (8 full blocks) ***)

let C2_STATE_EQ = prove
 (`!PK. PK < 2 EXP 8704
        ==> mld_shake256_state 1088 PK =
            word_xor (word_xor (mld_keccak_absorb_blocks 136 (word 0) PK 8)
                               (word(2 EXP 0 * 31)))
                     (word(2 EXP 1080 * 128))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[TRG_STATE_EQ 1088] THEN
  SUBGOAL_THEN `(PK DIV 2 EXP 8704) MOD 2 EXP 1088 = 0` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[DIV_LT; MOD_0]; REWRITE_TAC[WORD_XOR_0]]);;

(*** The statement: from the zeroing of the state (+0x21e8) to the return  ***)
(*** of the last permutation, the Keccak state at rsp0 + 32 that of the    ***)
(*** message mu || w1' of 1088 bytes                                       ***)

let C2_START = 0x21e8;;

let C2_STMT fn =
  parse_term(subst_tokens ["@FN@",fn; "@MC@",image_mc;
                           "@START@",string_of_int(layout fn + C2_START)]
  "exists f_events.
   forall e rsp0 pc MU W1.
     aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
     aligned 32 (rsp0:int64) /\\
     nonoverlapping (word_sub rsp0 (word 296),536) (word pc,libmldsa_size)
     ==> ensures x86
          (\\s. bytes_loaded s (word pc) @MC@ /\\
               read RIP s = word (pc + @START@) /\\
               read RSP s = rsp0 /\\
               read (memory :> bytes(word_add rsp0 (word 1408),64)) s = MU /\\
               read (memory :> bytes(word_add rsp0 (word 3584),1024)) s = W1 /\\
               read events s = e)
          (\\s. read RIP s = word (pc + @FN@_after_mldsa_keccakf1600_permute_23) /\\
               read RSP s = rsp0 /\\ read RBX s = word_add rsp0 (word 32) /\\
               read (memory :> wbytes (word_add rsp0 (word 32))) s =
               keccak_f1600 (mld_shake256_state 1088 (MU + 2 EXP 512 * W1)) /\\
               (exists e2. read events s = APPEND e2 e /\\
                  e2 = f_events (word_sub rsp0 (word 296)) pc /\\
                  memaccess_inbounds e2
                   [word_add rsp0 (word 1408),64; word_add rsp0 (word 3584),1024;
                    word_sub rsp0 (word 296),536;
                    word(pc + rodata_mld_KeccakF_RoundConstants),192]
                   [word_sub rsp0 (word 296),536]))
          (MAYCHANGE [RSP; RBX; R12; R13; R14; R15] ,,
           MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub rsp0 (word 296),296);
                      memory :> bytes(word_add rsp0 (word 32),208)])");;

(* the register facts of the pointers in the canonical form fb + n *)
let C2_REG_NORM_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read (r:(x86state,int64)component) s = word_add x y`) (concl th) &&
       not (frees (rhs(concl th)) = [])
    then CONV_RULE(RAND_CONV(REPEATC(CHANGED_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THENC
                            DEPTH_CONV NUM_ADD_CONV)) th
    else if can (term_match [] `read (r:(x86state,int64)component) s = x`) (concl th) &&
            frees (rhs(concl th)) = []
    then CONV_RULE(RAND_CONV WORD_REDUCE_CONV) th
    else th);;

(* the branch on concrete values (the loop test, the test of R15) *)
let C2_RIP_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read RIP s = (if c then x else y):int64`) (concl th) ||
       can (term_match [] `read events s = (e:(uarch_event)list)`) (concl th)
    then CONV_RULE(DEPTH_CONV WORD_RED_CONV THENC DEPTH_CONV INT_RED_CONV THENC
                   REWRITE_CONV[]) th
    else th);;

(*** One block k = 1..7 of the loop, from the state after its permutation ***)
(*** call at step n0 - 3 ... the loop head at step n0                     ***)

let C2_BLOCK_TAC execth k n0 =
  let a = tr_fb_add 328 in
  let ncall = n0 + 33 in
  let sn = mk_var("s"^string_of_int(n0 + 32),`:x86state`) in
  let sv = mk_var("st"^string_of_int k,`:1600 word`)
  and wv = mk_var("wb"^string_of_int k,`:1600 word`) in
  let w1 = `word_add fb (word 3880):int64` in
  let off j = 72 + 136 * (k - 1) + 16 * j in
  TR_STATE_CHUNKS_TAC a (0--7) (16--24) THEN
  MAP_EVERY (fun j -> C2_SRC_TAC k 128 (128 * j) w1 1024 (off j)) (0--7) THEN
  C2_SRC_TAC k 64 1024 w1 1024 (off 8) THEN
  TR_NAME_TAC (tr_st k) ("st"^string_of_int k) THEN
  TR_NAME_TAC (tr_wb k) ("wb"^string_of_int k) THEN
  X86_STEPS_TAC execth ((n0+1)--(n0+32)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO; VERIF_SUBWORD_JOIN_HI]) THEN
  C2_REG_NORM_TAC THEN
  MP_TAC(SPECL [a; sv; wv; sn] TR_BLK_MERGE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; CONJ_TAC THENL [ALL_TAC; CONJ_TAC THENL
     [ALL_TAC; TR_UNNAME_GOAL_TAC ("wb"^string_of_int k)]]] THEN
    TRG_ANTE_TAC 1088;
    DISCH_TAC] THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc execth "H_PERM"
   [`read RDI s`; mk_comb(mk_comb(`word_xor:1600 word->1600 word->1600 word`,sv),wv);
    `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   [`fb:int64`; `pc:num`] ncall THEN
  TR_UNNAME_TAC ("st"^string_of_int k) THEN
  TR_UNNAME_TAC ("wb"^string_of_int k) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TR_BLOCKS_STEP k]) THEN
  YMM_GHOST_TAC (mk_var("s"^string_of_int ncall,`:x86state`))
   ["YMM0","y0_"^string_of_int k; "YMM1","y1_"^string_of_int k] THEN
  X86_STEPS_TAC execth ((ncall+1)--(ncall+3)) THEN C2_RIP_TAC;;

let C2_TAC fn =
  let execth = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout fn + C2_START, layout (fn^"_after_mldsa_keccakf1600_permute_23"))] in
  let a = tr_fb_add 328 in
  let mu = `word_add fb (word 1704):int64` and w1 = `word_add fb (word 3880):int64` in
  let bound_tac src len =
    FIRST_ASSUM(fun th ->
      if can (term_match [] (subst [src,`a:int64`; mk_small_numeral len,`n:num`]
                `read (memory :> bytes(a,n)) (s:x86state) = x`)) (concl th)
      then let st = rand(lhs(concl th)) in
           let b = ISPECL [src; mk_small_numeral len;
                           mk_comb(`read memory:x86state->int64->byte`,st)] READ_BYTES_BOUND in
           ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
                       (REWRITE_RULE[GSYM READ_COMPONENT_COMPOSE; th] b))
      else NO_TAC) in
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERM" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(fb:int64) (pc:num). f_ev_all fb pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  X_GEN_TAC `e:(uarch_event)list` THEN WORD_FORALL_OFFSET_TAC 296 THEN
  MAP_EVERY X_GEN_TAC [`fb:int64`; `pc:num`; `MU:num`; `W1:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst execth] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  TR_ALIGNED_TAC 296 ((map (fun j -> 32 + 16 * j) (0--11)) @
                      [1408; 1424; 1440; 1456; 3584; 3600; 3616; 3632]) THEN
  ABBREV_TAC `PK = MU + 2 EXP 512 * W1` THEN
  GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
  GHOST_INTRO_TAC `ymm2_init:int256` `read YMM2` THEN
  GHOST_INTRO_TAC `ymm3_init:int256` `read YMM3` THEN
  FULL_INIT_TAC THEN
  bound_tac mu 64 THEN bound_tac w1 1024 THEN
  SUBGOAL_THEN `PK < 2 EXP 8704` ASSUME_TAC THENL
   [EXPAND_TAC "PK" THEN
    MATCH_MP_TAC(ARITH_RULE `a < 2 EXP 512 /\ b < 2 EXP 8192
                             ==> a + 2 EXP 512 * b < 2 EXP 8704`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the zeroing of the state from byte 32 *)
  X86_STEPS_TAC execth (1--2) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes128 (word_add fb (word 516))) s2 = x`)
           (concl th)
    then STRIP_ASSUME_TAC(CONV_RULE(READ_MEMORY_SPLIT_CONV 2) th) else NO_TAC) THEN
  ADDR_NORMALIZE_TAC THEN
  X86_STEPS_TAC execth (3--12) THEN
  MAP_EVERY (fun j ->
    FIRST_X_ASSUM(fun th ->
      if can (term_match [] (subst [mk_small_numeral (328 + 16 * j),`n:num`]
               `read (memory :> bytes128 (word_add fb (word n))) s12 = x`)) (concl th)
      then STRIP_ASSUME_TAC(CONV_RULE(READ_MEMORY_SPLIT_CONV 1) th) else NO_TAC)) (8--11) THEN
  ADDR_NORMALIZE_TAC THEN
  MP_TAC(CONV_RULE(RAND_CONV(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV))
     (READ_MEMORY_MERGE_CONV 1 `read (memory :> bytes64 (word_add fb (word 520))) s12`)) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN DISCH_TAC THEN
  (* block 0: mu and the first 72 bytes of w1' *)
  MAP_EVERY (fun j -> C2_SRC_TAC 0 128 (128 * j) mu 64 (16 * j)) (0--3) THEN
  MAP_EVERY (fun j -> C2_SRC_TAC 0 128 (512 + 128 * j) w1 1024 (16 * j)) (0--3) THEN
  C2_SRC_TAC 0 64 1024 w1 1024 64 THEN
  TR_NAME_TAC (tr_wb 0) "wb0" THEN
  X86_STEPS_TAC execth (13--39) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO; VERIF_SUBWORD_JOIN_HI]) THEN
  C2_REG_NORM_TAC THEN
  MP_TAC(SPECL [a; `word 0:1600 word`; `wb0:1600 word`; `s39:x86state`] TR_BLK_MERGE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; CONJ_TAC THENL [ALL_TAC; CONJ_TAC THENL
     [ALL_TAC; TR_UNNAME_GOAL_TAC "wb0"]]] THEN
    TRG_ANTE_TAC 1088;
    DISCH_TAC] THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc execth "H_PERM"
   [`read RDI s`; `word_xor (word 0) wb0:1600 word`;
    `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   [`fb:int64`; `pc:num`] 40 THEN
  TR_UNNAME_TAC "wb0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TR_BLOCKS_STEP 0]) THEN
  YMM_GHOST_TAC `s40:x86state` ["YMM0","y0_0"; "YMM1","y1_0"] THEN
  X86_STEPS_TAC execth (41--43) THEN
  (* the loop, 7 blocks *)
  MAP_EVERY (fun k -> C2_BLOCK_TAC execth k (43 + 36 * (k - 1))) (1--7) THEN
  (* the test of the rest, the padding and the last permutation *)
  X86_STEPS_TAC execth (296--297) THEN C2_RIP_TAC THEN
  TR_STATE_CHUNKS_TAC a [] ((1--15) @ (17--24)) THEN
  TR_STATE_BYTES_TAC a ((0--7) @ (128--135)) THEN
  TR_NAME_TAC (tr_st 8) "st8" THEN
  X86_STEPS_TAC execth (298--304) THEN
  MP_TAC(SPECL [a; `st8:1600 word`; `s304:x86state`] TR_PAD0_MERGE) THEN
  ANTS_TAC THENL [TRG_ANTE_TAC 1088; DISCH_TAC] THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc execth "H_PERM"
   [`read RDI s`;
    `word_xor (word_xor st8 (word(2 EXP 0 * 31))) (word(2 EXP 1080 * 128)):1600 word`;
    `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   [`fb:int64`; `pc:num`] 305 THEN
  TR_UNNAME_TAC "st8" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM(MATCH_MP C2_STATE_EQ (ASSUME `PK < 2 EXP 8704`))]) THEN
  C2_REG_NORM_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let PROVE_C2_87 fn = prove(C2_STMT fn, C2_TAC fn);;

(* ------------------------------------------------------------------------- *)
(* The comparison of c~ (cc0..cc3 at rsp0 + 1344 ...) with c2 (dd0..dd3 at   *)
(* rsp0 + 1472 ...), 64 bytes, as clang 23 vectorizes mld_ct_memcmp for      *)
(* ML-DSA-87: as CMP44 with four chunks and no scalar part.                  *)
(* ------------------------------------------------------------------------- *)

(* aligned 16 (rsp0 + off) for the offsets offs, from that of rsp0 + base *)
let VM_ALIGNED16_RSP0_TAC offs base =
  MAP_EVERY (fun off ->
    SUBGOAL_THEN (subst [mk_small_numeral off,`n:num`]
                    `aligned 16 (word_add rsp0 (word n):int64)`) ASSUME_TAC THENL
     [SUBST1_TAC(WORD_RULE(subst [mk_small_numeral off,`n:num`; mk_small_numeral base,`b:num`;
                                  mk_small_numeral (off - base),`m:num`]
        `word_add (rsp0:int64) (word n) = word_add (word_add rsp0 (word b)) (word m)`)) THEN
      MATCH_MP_TAC ALIGNED_WORD_ADD THEN ASM_REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN
      REWRITE_TAC[];
      ALL_TAC]) offs;;

let CMP87_STMT fn =
  parse_term(subst_tokens ["@FN@",fn; "@MC@",image_mc;
                           "@START@",string_of_int(layout fn + 0x2572)]
  "exists f_events.
  forall e rsp0 pc (cc0:int128) (cc1:int128) (cc2:int128) (cc3:int128)
         (dd0:int128) (dd1:int128) (dd2:int128) (dd3:int128).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    aligned 16 (word_add rsp0 (word 1344)) /\\ aligned 16 (word_add rsp0 (word 1472))
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) @MC@ /\\
              read RIP s = word (pc + @START@) /\\
              read RSP s = rsp0 /\\
              read (memory :> bytes128 (word_add rsp0 (word 1344))) s = cc0 /\\
              read (memory :> bytes128 (word_add rsp0 (word 1360))) s = cc1 /\\
              read (memory :> bytes128 (word_add rsp0 (word 1376))) s = cc2 /\\
              read (memory :> bytes128 (word_add rsp0 (word 1392))) s = cc3 /\\
              read (memory :> bytes128 (word_add rsp0 (word 1472))) s = dd0 /\\
              read (memory :> bytes128 (word_add rsp0 (word 1488))) s = dd1 /\\
              read (memory :> bytes128 (word_add rsp0 (word 1504))) s = dd2 /\\
              read (memory :> bytes128 (word_add rsp0 (word 1520))) s = dd3 /\\
              read events s = e)
         (\\s. read RIP s = word (pc + @FN@_join2) /\\
              read RSP s = rsp0 /\\
              read R14 s = (if cc0 = dd0 /\\ cc1 = dd1 /\\ cc2 = dd2 /\\ cc3 = dd3
                            then word 0 else word 4294967290) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rsp0 pc /\\
                 memaccess_inbounds e2 [word_add rsp0 (word 1344),64; word_add rsp0 (word 1472),64]
                                       []))
         (MAYCHANGE [RIP; RAX; RCX; RDX; R14] ,, MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])");;

let CMP87_SETUP_TAC execth =
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (pc:num). f_ev_all rsp0 pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `pc:num`;
    `cc0:int128`; `cc1:int128`; `cc2:int128`; `cc3:int128`;
    `dd0:int128`; `dd1:int128`; `dd2:int128`; `dd3:int128`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst execth] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  VM_ALIGNED16_RSP0_TAC [1360; 1376; 1392] 1344 THEN
  VM_ALIGNED16_RSP0_TAC [1488; 1504; 1520] 1472 THEN
  GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
  GHOST_INTRO_TAC `ymm2_init:int256` `read YMM2` THEN
  GHOST_INTRO_TAC `ymm3_init:int256` `read YMM3` THEN
  GHOST_INTRO_TAC `ymm4_init:int256` `read YMM4` THEN
  FULL_INIT_TAC THEN
  (fun g -> abbrev_ctr () := 0; ALL_TAC g);;

(* The 47 steps abbreviate the XOR of the chunks (ab1..ab4), their OR (ab8)
   folded to one byte (ab17), and the test of that byte (ab29..ab33). *)
let CMP87_TAC execth =
  CMP87_SETUP_TAC execth THEN
  ABBREV_STEPS_TAC execth (1--47) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ab33:int64 = if word_zx (ab17:int64):byte = word 0
                             then word 0 else word 4294967290` SUBST1_TAC THENL
   [UNFOLD_ABBREVS_TAC (abn [33;32;31;30;29]) THEN REWRITE_TAC[WORD_VAL_MOD_256] THEN
    CONV_TAC BITBLAST_RULE;
    ALL_TAC] THEN
  SUBGOAL_THEN `(word_zx (ab17:int64):byte = word 0) <=> (ab8:int128 = word 0)`
   SUBST1_TAC THENL
   [UNFOLD_ABBREVS_TAC (abn [17;16;15;14;13;12;11;10;9]) THEN
    REWRITE_TAC[WORD_VAL_MOD_256] THEN CONV_TAC BITBLAST_RULE;
    ALL_TAC] THEN
  SUBGOAL_THEN `(ab8:int128 = word 0) <=>
                (cc0:int128) = dd0 /\ (cc1:int128) = dd1 /\
                (cc2:int128) = dd2 /\ (cc3:int128) = dd3`
   SUBST1_TAC THENL
   [UNFOLD_ABBREVS_TAC (abn [8;7;5;4;3;2;1]) THEN CONV_TAC BITBLAST_RULE;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let PROVE_CMP87 fn =
  let execth = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout fn + 0x2572, layout fn + 0x2659)] in
  prove(CMP87_STMT fn, CMP87_TAC execth);;
