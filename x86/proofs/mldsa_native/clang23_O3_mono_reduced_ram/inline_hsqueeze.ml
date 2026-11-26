(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The padding and the squeeze of mld_H44/65/87 of the clang 23 -O3 build,   *)
(* from the end of the absorbs to the zeroing of the state. mld_H44/65       *)
(* (HXS_STMT/HXS_TAC): pad the state at the position p and at byte 135       *)
(* (bytes8 split/join as in x86-B's SPONGE_FIN_TAC), then K = max 1          *)
(* (ceil(outlen/136)) times permute the state and copy min(rest,136) bytes   *)
(* of it to out + 136 k with memcpy. The two ends of an iteration (the last  *)
(* block or not) are one goal: the arithmetic is proved by cases and the     *)
(* events are discharged once. mld_H87 (HXS64_STMT/HXS64_TAC): the padding,  *)
(* one permutation and the copy of the first 64 bytes. Also the helpers      *)
(* HX_NOV_SHRINK_TAC for the top level.                                      *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_hphase.ml";;
needs "common/fips204/properties/mldsa_native_squeeze.ml";;
needs "common/mldsa_native_sampling.ml";;
needs "x86/proofs/utils/mldsa_native_hash.ml";;

type hx_sq = { sq_fn : string; sq_entry : int; sq_head : int; sq_exit : int; sq_so : int; sq_fr : int };;

let sq_tok q s = subst_tokens
  ["@ENTRY@",string_of_int (layout q.sq_fn + q.sq_entry); "@EXIT@",string_of_int (layout q.sq_fn + q.sq_exit);
   "@SA@",string_of_int (296 + q.sq_so); "@FR@",string_of_int q.sq_fr] s;;

let HXS_STMT q = parse_term(sq_tok q
 "!mc ea el ev.
   memcpy_full_contract mc ea el ev
   ==> exists f_events. forall e bq p (S:1600 word) out outlen pc.
     p < 136 /\\
     aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
     nonoverlapping (out,outlen) (bq,@FR@) /\\
     ALLPAIRS nonoverlapping [(out,outlen); (bq,@FR@)]
       [(word pc,libmldsa_size); (word(pc + got_memcpy),8); (ea,el)]
     ==> ensures x86
      (\\s. bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
           read RIP s = word (pc + @ENTRY@) /\\ read RSP s = word_add bq (word 296) /\\
           read R15 s = word p /\\ read RBP s = out /\\ read RBX s = word outlen /\\
           (read DF s <=> false) /\\
           read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
           read (memory :> bytes(ea,el)) s = ev /\\
           read (memory :> wbytes (word_add bq (word @SA@))) s = S /\\
           read events s = e)
      (\\s. read RIP s = word (pc + @EXIT@) /\\ read RSP s = word_add bq (word 296) /\\
           read (memory :> bytes(out,outlen)) s =
             num_of_bytelist (list_of_seq (mld_keccak_squeeze_byte 136 (mld_keccak_finalize 136 31 S p) 136) outlen) /\\
           (exists e2. read events s = APPEND e2 e /\\ e2 = f_events bq p out outlen mc pc /\\
              memaccess_inbounds e2 [out,outlen; bq,@FR@; word(pc + got_memcpy),8; ea,el;
                                     word(pc + rodata_mld_KeccakF_RoundConstants),192]
                                    [out,outlen; bq,@FR@]))
      (MAYCHANGE [RIP; RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [RBX; R12; R13; R14; R15] ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(out,outlen); memory :> bytes(bq,296);
                  memory :> bytes(word_add bq (word @SA@),204)])");;

let HXS_INV q = parse_term(sq_tok q
 "\\k s. read RSP s = word_add bq (word 296) /\\ read RBP s = out /\\
        read R15 s = word_add bq (word @SA@) /\\
        read R12 s = word (MIN outlen (136 * k)) /\\ read RBX s = word (outlen - 136 * k) /\\
        (k < K ==> read R13 s = word 136) /\\
        (read DF s <=> false) /\\
        read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
        read (memory :> bytes(ea,el)) s = ev /\\
        read (memory :> bytes(word_add bq (word @SA@),200)) s = val(keccak_squeeze k Sf) /\\
        read (memory :> bytes(out,MIN outlen (136 * k))) s =
          num_of_bytelist (list_of_seq (mld_keccak_squeeze_byte 136 Sf 136) (MIN outlen (136 * k)))");;

let H44_SQ = { sq_fn = "mld_H44"; sq_entry = 0x72f; sq_head = 0x792; sq_exit = 0x7bc; sq_so = 16; sq_fr = 528 };;

let HXS_INTRO_TAC q =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
               [layout_range q.sq_fn; layout_range "mldsa_keccakf1600_permute"; layout_range "plt_memcpy"] in
  REPEAT GEN_TAC THEN DISCH_THEN(fun mcp ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memcpy_full_contract] mcp) "H_MEMCPY") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   (SPONGE_RENAME_E2 MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600) "H_PERM" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(bq:int64) (p:num) (out:int64) (outlen:num) (mc:int64) (pc:num).
      APPEND (f_ev_epil bq p out outlen mc pc)
       (APPEND (ENUMERATEL (if outlen = 0 then 1 else (outlen + 135) DIV 136)
                  (\i. f_ev_loop bq p out outlen mc pc i)) (f_ev_prol bq p out outlen mc pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `bq:int64`; `p:num`; `S:1600 word`; `out:int64`; `outlen:num`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN (parse_term(Printf.sprintf "%d + outlen <= 2 EXP 64" q.sq_fr)) ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(bq:int64)`; `val(out:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `K = if outlen = 0 then 1 else (outlen + 135) DIV 136` THEN
  ABBREV_TAC `Sf = mld_keccak_finalize 136 31 S p` THEN
  SUBGOAL_THEN `~(K = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN COND_CASES_TAC THEN REWRITE_TAC[ARITH_EQ] THEN
    SIMP_TAC[DIV_EQ_0; ARITH_EQ] THEN UNDISCH_TAC `~(outlen = 0)` THEN ARITH_TAC; ALL_TAC];;

(* the number of blocks K of the squeeze *)
let HXS_K = prove
 (`!outlen k K. (if outlen = 0 then 1 else (outlen + 135) DIV 136) = K /\ k < K
     ==> MIN outlen (136 * k) = 136 * k /\ 136 * k <= outlen /\
         (k + 1 < K <=> 136 < outlen - 136 * k) /\
         (k + 1 < K ==> MIN outlen (136 * (k + 1)) = 136 * (k + 1)) /\
         (~(k + 1 < K) ==> MIN outlen (136 * (k + 1)) = outlen /\ outlen - 136 * (k + 1) = 0 /\
                           outlen - 136 * k <= 136)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `k = 0` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[MIN] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[ARITH_RULE `k < n <=> k + 1 <= n`] THEN
    SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN REWRITE_TAC[MIN] THEN
    REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC]);;

let hasc n c = can (find_term (fun t -> is_const t && fst(dest_const t) = n)) c;;
(* j < 200 for the bytes of the state: a numeral, p < 136 or j < 200 *)
let HXS_LT200_TAC =
  CONV_TAC NUM_REDUCE_CONV THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         FIRST_ASSUM(fun th -> if can (term_match [] `p < 136`) (concl th)
                               then MP_TAC th THEN ARITH_TAC else NO_TAC)];;

(* the bytes8 facts of the state at a (forall j < 200, at word_add a (word j)) *)
let hxs_is_allbytes s th =
  let c = concl th in is_forall c && hasc "bytes8" c && free_in s c &&
  not (can (find_term is_neg) c);;

(* split off byte jt of the forall fact of the current state, at the address *)
(* addr of the simulation (proved equal to word_add a (word jt) by tac)      *)
let HXS_SPLIT_TAC jt addr tac =
  W(fun (asl,w) -> let s = hx_cur_state asl in
    FIRST_X_ASSUM(fun th ->
      if not(hxs_is_allbytes s th) then NO_TAC else
      let j,bod = dest_forall(concl th) in
      let l = lhs(rand bod) and r = rand(rand bod) in
      let l' = subst [jt,j] l in
      let fact = mk_eq(subst [addr,rand(rand(rand(rator l')))] l', subst [jt,j] r) in
      ASSUME_TAC(SPONGE_RESTRICT_NE jt th) THEN
      SUBGOAL_THEN fact ASSUME_TAC THENL
       [SUBGOAL_THEN (mk_eq(addr,rand(rand(rand(rator(subst [jt,j] l)))))) SUBST1_TAC THENL
         [tac; MATCH_MP_TAC(SPEC jt th) THEN HXS_LT200_TAC];
        ALL_TAC]));;

(* rebuild the forall fact of the current state after the XOR of byte jt   *)
(* with the constant c (the facts for j <> jt and for jt at addr)           *)
let HXS_JOIN_TAC jt c addr tac =
  W(fun (asl,w) -> let s = hx_cur_state asl in
    let rth = find (fun th -> let k = concl th in is_forall k && hasc "bytes8" k && free_in s k &&
                                can (find_term is_neg) k) (map snd asl) in
    let j,bod = dest_forall(concl rth) in
    let l = lhs(rand bod) and r = rand(rand bod) in
    let x = lhand r in
    let a = lhand(rand(rand(rand(rator l)))) in
    let x' = mk_binop `word_xor:1600 word->1600 word->1600 word` x
               (mk_comb(`word:num->1600 word`,mk_binop `( * ):num->num->num`
                  (mk_binop `EXP` `2` (mk_binop `( * ):num->num->num` `8` jt)) c)) in
    let goal = mk_forall(j,mk_imp(mk_binop `(<):num->num->bool` j `200`,
                 mk_eq(l,subst [x',x] r))) in
    SUBGOAL_THEN goal ASSUME_TAC THENL
     [X_GEN_TAC j THEN DISCH_TAC THEN
      MP_TAC(SPECL [x; jt; j; c] SPONGE_BYTE_AT) THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THEN HXS_LT200_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN COND_CASES_TAC THENL
       [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = j then SUBST_ALL_TAC th else NO_TAC) THEN
        SUBGOAL_THEN (mk_eq(mk_comb(mk_comb(`word_add:int64->int64->int64`,a),mk_comb(`word:num->int64`,jt)),addr)) SUBST1_TAC THENL
         [tac; CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[]];
        FIRST_ASSUM(fun th -> if th = rth then MATCH_MP_TAC th else NO_TAC) THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if th = rth then ALL_TAC else NO_TAC));;

(* the padding of S at p and at 135 (the first three instructions, from      *)
(* FULL_INIT_TAC): the state at bq + sa is then Sf in bytes form, at s3      *)
let HXS_PAD_TAC sa exec =
  let st = mk_comb(`word_add (bq:int64)`,mk_comb(`word:num->int64`,mk_small_numeral sa)) in
  let addr_p = if sa = 296 then `word_add (bq:int64) (word (296 + 1 * val (word p:int64)))`
               else subst [mk_small_numeral (sa - 16),`k:num`] `word_add (bq:int64) (word (k + 1 * val (word p:int64) + 16))` in
  let addr_135 = mk_comb(`word_add (bq:int64)`,mk_comb(`word:num->int64`,mk_small_numeral (sa + 135))) in
  let addr_tac = REWRITE_TAC[MATCH_MP TG_VALR (ASSUME `p < 136`)] THEN CONV_TAC WORD_RULE in
  FULL_INIT_TAC THEN
  FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> wbytes a) s0 = X`) (concl th)
                        then ASSUME_TAC(MATCH_MP SPONGE_ALL_BYTES_OF_WBYTES th) else NO_TAC) THEN
  X86_STEPS_TAC exec (1--1) THEN HX_RES (hx_p32 `p:num`) THEN
  HXS_SPLIT_TAC `p:num` addr_p addr_tac THEN
  X86_STEPS_TAC exec (2--2) THEN
  SUBGOAL_THEN `p < 200` ASSUME_TAC THENL [UNDISCH_TAC `p < 136` THEN ARITH_TAC; ALL_TAC] THEN
  HXS_JOIN_TAC `p:num` `31` addr_p addr_tac THEN
  HXS_SPLIT_TAC `135` addr_135 (CONV_TAC WORD_RULE) THEN
  X86_STEPS_TAC exec (3--3) THEN
  HXS_JOIN_TAC `135` `128` addr_135 (CONV_TAC WORD_RULE) THEN
  SUBGOAL_THEN (subst [st,`st:int64`] `read (memory :> bytes(st,200)) s3 = val(Sf:1600 word)`) ASSUME_TAC THENL
   [REWRITE_TAC[GSYM READ_MEMORY_WBYTES_1600] THEN EXPAND_TAC "Sf" THEN REWRITE_TAC[mld_keccak_finalize] THEN
    REWRITE_TAC[ARITH_RULE `136 - 1 = 135`] THEN MATCH_MP_TAC SPONGE_WBYTES_OF_ALL_BYTES THEN
    FIRST_ASSUM(fun th -> if hxs_is_allbytes `s3:x86state` th then ACCEPT_TAC th else NO_TAC); ALL_TAC];;

(* the prologue of the squeeze loop: the padding, then the loop registers    *)
let HXS_PROL_TAC q exec =
  HXS_PAD_TAC (296 + q.sq_so) exec THEN
  X86_STEPS_TAC exec (4--8) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; SUB_0; keccak_squeeze; ARITH_RULE `MIN n 0 = 0`;
    READ_MEMORY_BYTES_TRIVIAL; list_of_seq; num_of_bytelist; LT_NZ] THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_REDUCE_CONV THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let HXS_SQ_SUC = prove(`!(S:1600 word) i. keccak_f1600 (keccak_squeeze i S) = keccak_squeeze (i + 1) S`,
  REWRITE_TAC[GSYM ADD1; keccak_squeeze]);;

let HXS_CMOV = prove
 (`!x. (if x < 136 then word x else word 136):int64 = word (MIN x 136)`,
  GEN_TAC THEN REWRITE_TAC[MIN] THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN ASM_ARITH_TAC);;

(* the output after block k: the bytes of block k + 1 appended *)
let HXS_OUT = prove
 (`!(S:1600 word) k r (s:x86state) out.
     r <= 136 /\
     read (memory :> bytes(out,136 * k)) s =
       num_of_bytelist (list_of_seq (mld_keccak_squeeze_byte 136 S 136) (136 * k)) /\
     read (memory :> bytes(word_add out (word (136 * k)),r)) s =
       val(keccak_squeeze (k + 1) S) MOD 2 EXP (8 * r)
     ==> read (memory :> bytes(out,136 * k + r)) s =
         num_of_bytelist (list_of_seq (mld_keccak_squeeze_byte 136 S 136) (136 * k + r))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MLD_LIST_OF_SEQ_ADD; NUM_OF_BYTELIST_APPEND; LENGTH_LIST_OF_SEQ] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(SPECL [`136`; `S:1600 word`; `136`; `136 * k`; `k + 1`; `0`; `r:num`] SQUEEZE_CHUNK) THEN
  ANTS_TAC THENL [UNDISCH_TAC `r <= 136` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC);;

(* the exit test of iteration k (after the copy of r bytes) *)
let HXS_TEST = prove
 (`!outlen k K r. (k + 1 < K <=> 136 < outlen - 136 * k) /\ MIN (outlen - 136 * k) 136 = r
     ==> (outlen - 136 * k - r = 0 <=> ~(k + 1 < K))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[MIN] THEN ARITH_TAC);;

let HXS_BODY_TAC q exec =
  let vars = [`bq:int64`; `p:num`; `out:int64`; `outlen:num`; `mc:int64`; `pc:num`; `k:num`] in
  let st = mk_comb(`word_add (bq:int64)`,mk_comb(`word:num->int64`,mk_small_numeral (296 + q.sq_so))) in
  let plt = layout "plt_memcpy" in
  let hd = mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral (layout q.sq_fn + q.sq_head))
  and ex = mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral (layout q.sq_fn + q.sq_exit)) in
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(SPECL [`outlen:num`; `k:num`; `K:num`] HXS_K) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FULL_INIT_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `MIN outlen (136 * k) = 136 * k`]) THEN
  (* the permutation *)
  HX_DRIVE_TAC exec [] (layout "mldsa_keccakf1600_permute") THEN
  KECCAK_STATE_WBYTES_TAC `keccak_squeeze k Sf` THEN
  HX_LCALL_TAC exec "H_PERM" [`read RDI s`; `keccak_squeeze k Sf`; `pc:num`; `read RSP s`;
                              `read (memory :> bytes64 (read RSP s)) s`] vars THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HXB_WORD_ADD_8; HXS_SQ_SUC; READ_MEMORY_WBYTES_1600]) THEN
  (* r = min(rest,136) bytes to copy *)
  SUBGOAL_THEN `val(word (outlen - 136 * k):int64) = outlen - 136 * k` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC (parse_term(Printf.sprintf "%d + outlen <= 2 EXP 64" q.sq_fr)) THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `r = MIN (outlen - 136 * k) 136` THEN
  SUBGOAL_THEN `r <= 136 /\ r <= outlen - 136 * k /\ val(word r:int64) = r` STRIP_ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `MIN (outlen - 136 * k) 136 = r`)) THEN REPEAT CONJ_TAC THENL
     [ARITH_TAC; ARITH_TAC; MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64; MIN] THEN ARITH_TAC]; ALL_TAC] THEN
  HX_DRIVE_TAC exec [ASSUME `val(word (outlen - 136 * k):int64) = outlen - 136 * k`; HXS_CMOV;
                     ASSUME `MIN (outlen - 136 * k) 136 = r`] plt THEN
  HX_RESTATE_TAC `RDI` `word_add out (word (136 * k)):int64` (REWRITE_TAC[MULT_CLAUSES; WORD_VAL] THEN CONV_TAC WORD_RULE) THEN
  W(fun (asl,w) -> LIBC_PLT_TAC exec plt (layout "got_memcpy") (hx_state_num asl)) THEN
  W(fun (asl,w) -> let s = hx_cur_state asl in
    SUBGOAL_THEN (subst [s,`s:x86state`; st,`st:int64`]
      `read (memory :> bytes(st,r)) s = val(keccak_squeeze (k + 1) (Sf:1600 word)) MOD 2 EXP (8 * r)`) ASSUME_TAC THENL
     [MP_TAC(SPECL [st; `200`; `val(keccak_squeeze (k + 1) (Sf:1600 word))`; `0`; `r:num`; s] READ_MEMORY_BYTES_SUB) THEN
      REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; EXP; DIV_1; ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `r <= 136` THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN (subst [s,`s:x86state`; st,`st:int64`]
      `read (memory :> bytes(st,val(word r:int64))) s = val(keccak_squeeze (k + 1) (Sf:1600 word)) MOD 2 EXP (8 * r)`) ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  W(fun (asl,w) -> let k0 = hx_state_num asl in
    REMOVE_THEN "H_MEMCPY" (fun th ->
      LIBC_CONTRACT_SIM_TAC ~is_safety_thm:true exec th
       [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
        `val(keccak_squeeze (k + 1) (Sf:1600 word)) MOD 2 EXP (8 * r)`;
        `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`] (k0+1) THENL
       [HX_E2_ANY vars; LABEL_TAC "H_MEMCPY" th])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE `word_add (word_sub (x:int64) (word 8)) (word 8) = x`]) THEN
  (* the test: rest - r = 0 iff this is the last block *)
  SUBGOAL_THEN `word_sub (word (outlen - 136 * k)) (word r):int64 = word (outlen - 136 * k - r) /\
                val(word (outlen - 136 * k - r):int64) = outlen - 136 * k - r` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_SIMP_TAC[WORD_SUB]; MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      UNDISCH_TAC (parse_term(Printf.sprintf "%d + outlen <= 2 EXP 64" q.sq_fr)) THEN ARITH_TAC]; ALL_TAC] THEN
  ASSUME_TAC(MP (SPECL [`outlen:num`; `k:num`; `K:num`; `r:num`] HXS_TEST)
    (CONJ (ASSUME `k + 1 < K <=> 136 < outlen - 136 * k`) (ASSUME `MIN (outlen - 136 * k) 136 = r`))) THEN
  W(fun (asl,w) -> let k0 = hx_state_num asl in X86_STEPS_TAC exec ((k0+1)--(k0+4))) THEN
  HX_RES [ASSUME `word_sub (word (outlen - 136 * k)) (word r):int64 = word (outlen - 136 * k - r)`;
          ASSUME `val(word (outlen - 136 * k - r):int64) = outlen - 136 * k - r`;
          ASSUME `outlen - 136 * k - r = 0 <=> ~(k + 1 < K)`; COND_SWAP] THEN
  (* the state after the iteration, the same in both cases (last block or  *)
  (* not): the arithmetic facts by cases, then one discharge of the events  *)
  SUBGOAL_THEN `(k + 1 < K ==> r = 136) /\ MIN outlen (136 * (k + 1)) = 136 * k + r /\
                outlen - 136 * (k + 1) = outlen - 136 * k - r` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`k + 1 < K <=> 136 < outlen - 136 * k`; `MIN (outlen - 136 * k) 136 = r`;
                           `136 * k <= outlen`] THEN
    REWRITE_TAC[MIN] THEN ARITH_TAC; ALL_TAC] THEN
  HX_RESTATE_TAC `RIP` (mk_comb(`word:num->int64`,mk_cond(`k + 1 < K`,hd,ex)))
    (REWRITE_TAC[GSYM NOT_LT] THEN ASM_CASES_TAC `k + 1 < K` THEN FIRST_X_ASSUM(fun th -> REWRITE_TAC[th])) THEN
  HX_RESTATE_TAC `R12` `word (136 * k + r):int64`
    (FIRST [REWRITE_TAC[WORD_ADD] THEN NO_TAC; CONV_TAC WORD_RULE]) THEN
    W(fun (asl,w) -> let s = hx_cur_state asl in
    SUBGOAL_THEN (subst [s,`s:x86state`] `k + 1 < K ==> read R13 s = word 136`) ASSUME_TAC THENL
     [DISCH_THEN(ASSUME_TAC o MP (ASSUME `k + 1 < K ==> r = 136`)) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
      SUBGOAL_THEN (subst [s,`s:x86state`]
        `read (memory :> bytes(out,136 * k + r)) s =
         num_of_bytelist (list_of_seq (mld_keccak_squeeze_byte 136 Sf 136) (136 * k + r))`) ASSUME_TAC THENL
       [MATCH_MP_TAC HXS_OUT THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  (* the goal with the test k + 1 < K, and no equivalences with it in the  *)
  (* final rewriting                                                       *)
  REWRITE_TAC[GSYM(ASSUME `k + 1 < K <=> 136 < outlen - 136 * k`)] THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_iff(concl th) && free_in `k + 1 < K` (concl th) then ALL_TAC else NO_TAC)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `MIN (outlen - 136 * k) 136 = r`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `(if outlen = 0 then 1 else (outlen + 135) DIV 136) = K`)) THEN
  SIGN_LOOP_DISCHARGE_TAC;;

let HXS_KMIN = prove
 (`!outlen K. (if outlen = 0 then 1 else (outlen + 135) DIV 136) = K ==> MIN outlen (136 * K) = outlen`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(SPECL [`outlen + 135`; `136`] DIVISION) THEN ARITH_TAC);;

let HXS_TAC q =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
               [layout_range q.sq_fn; layout_range "mldsa_keccakf1600_permute"; layout_range "plt_memcpy"] in
  let hd = mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral (layout q.sq_fn + q.sq_head))
  and ex = mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral (layout q.sq_fn + q.sq_exit)) in
  HXS_INTRO_TAC q THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `K:num` hd ex (HXS_INV q) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    HXS_PROL_TAC q exec;
    HXS_BODY_TAC q exec;
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    MP_TAC(SPECL [`outlen:num`; `K:num`] HXS_KMIN) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `MIN outlen (136 * K) = outlen`]) THEN
    EXPAND_TAC "Sf" THEN ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC];;

let HXS_PROVE q = prove(HXS_STMT q, HXS_TAC q);;

(* ------------------------------------------------------------------------- *)
(* mld_H87: a fixed output of 64 bytes. From the end of the absorbs to the   *)
(* zeroing of the state: the padding as above, one permutation, and the      *)
(* copy of the first 64 bytes of the state (4 loads with MOVAPS, 4 stores    *)
(* with MOVUPS) to out, whose address the code reads from the stack slot at  *)
(* bq + sq_out.                                                              *)
(* ------------------------------------------------------------------------- *)

type hx_sq64 = { s6_fn : string; s6_entry : int; s6_exit : int; s6_so : int; s6_fr : int; s6_out : int };;

let s6_tok q s = subst_tokens
  ["@ENTRY@",string_of_int (layout q.s6_fn + q.s6_entry); "@EXIT@",string_of_int (layout q.s6_fn + q.s6_exit);
   "@SA@",string_of_int (296 + q.s6_so); "@FR@",string_of_int q.s6_fr; "@OUT@",string_of_int q.s6_out] s;;

let HXS64_STMT q = parse_term(s6_tok q
 "exists f_events. forall e bq p (S:1600 word) out pc.
   p < 136 /\\ aligned 16 (word_add bq (word @SA@):int64) /\\
   aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   nonoverlapping (out,64) (bq,@FR@) /\\ nonoverlapping (word pc,libmldsa_size) (bq,@FR@) /\\
   nonoverlapping (word pc,libmldsa_size) (out,64)
   ==> ensures x86
    (\\s. bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
         read RIP s = word (pc + @ENTRY@) /\\ read RSP s = word_add bq (word 296) /\\
         read R15 s = word p /\\
         read (memory :> bytes64 (word_add bq (word @OUT@))) s = out /\\
         read (memory :> wbytes (word_add bq (word @SA@))) s = S /\\
         read events s = e)
    (\\s. read RIP s = word (pc + @EXIT@) /\\ read RSP s = word_add bq (word 296) /\\
         read (memory :> bytes(out,64)) s =
           num_of_bytelist (list_of_seq (mld_keccak_squeeze_byte 136 (mld_keccak_finalize 136 31 S p) 136) 64) /\\
         (exists e2. read events s = APPEND e2 e /\\ e2 = f_events bq p out pc /\\
            memaccess_inbounds e2 [out,64; bq,@FR@; word(pc + rodata_mld_KeccakF_RoundConstants),192]
                                  [out,64; bq,@FR@]))
    (MAYCHANGE [RIP; RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [RBX] ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bytes(out,64); memory :> bytes(bq,296);
                memory :> bytes(word_add bq (word @SA@),204)])");;

let HXS64_DIGEST = prove
 (`!(S:1600 word). num_of_bytelist(list_of_seq (mld_keccak_squeeze_byte 136 S 136) 64) =
                   val(word_subword (keccak_f1600 S) (0,512):512 word)`,
  GEN_TAC THEN
  SUBGOAL_THEN `list_of_seq (mld_keccak_squeeze_byte 136 S 136) 64 =
                list_of_seq (\j. word_subword (keccak_f1600 S) (8*j,8):byte) 64` SUBST1_TAC THENL
   [MATCH_MP_TAC LIST_OF_SEQ_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[mld_keccak_squeeze_byte] THEN
    SUBGOAL_THEN `(136 + i) DIV 136 = 1 /\ (136 + i) MOD 136 = i` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `i:num`; MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1`] THEN
      UNDISCH_TAC `i < 64` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `1 = SUC 0`; keccak_squeeze];
    ALL_TAC] THEN
  MP_TAC(SPECL [`keccak_f1600 S`; `64`] SPONGE_NBL_SEQ) THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_CONV `dimindex(:1600)`; DIMINDEX_CONV `dimindex(:512)`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[EXP; DIV_1]);;

let HXS64_TAC q =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
               [layout_range q.s6_fn; layout_range "mldsa_keccakf1600_permute"] in
  let sa = 296 + q.s6_so in
  let st = mk_comb(`word_add (bq:int64)`,mk_comb(`word:num->int64`,mk_small_numeral sa)) in
  let vars = [`bq:int64`; `p:num`; `out:int64`; `pc:num`] in
  let norm = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC DEPTH_CONV NUM_ADD_CONV) in
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   (SPONGE_RENAME_E2 MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600) "H_PERM" THEN
  CONCRETIZE_F_EVENTS_TAC `\(bq:int64) (p:num) (out:int64) (pc:num). f_ev_s bq p out pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `bq:int64`; `p:num`; `S:1600 word`; `out:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ABBREV_TAC `Sf = mld_keccak_finalize 136 31 S p` THEN
  HXS_PAD_TAC sa exec THEN
  (* the permutation *)
  HX_DRIVE_TAC exec [] (layout "mldsa_keccakf1600_permute") THEN
  KECCAK_STATE_WBYTES_TAC `Sf:1600 word` THEN
  HX_LCALL_TAC exec "H_PERM" [`read RDI s`; `Sf:1600 word`; `pc:num`; `read RSP s`;
                              `read (memory :> bytes64 (read RSP s)) s`] vars THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HXB_WORD_ADD_8]) THEN
  (* the four chunks of the permuted state, at aligned addresses *)
  FIRST_ASSUM(fun ra -> if concl ra = mk_comb(`aligned 16:int64->bool`,st) then
    ASSUME_TAC(norm(REWRITE_RULE[WORD_ADD_0] ra)) THEN
    MAP_EVERY (fun k -> let th = MATCH_MP ALIGNED_WORD_ADD (CONJ ra (SPONGE_A16 k)) in
                        ASSUME_TAC th THEN ASSUME_TAC(norm th)) [16;32;48]
    else NO_TAC) THEN
  W(fun (asl,w) -> let s = hx_cur_state asl in
    FIRST_ASSUM(fun wth ->
      if concl wth <> subst [st,`st:int64`; s,`s:x86state`]
           `read (memory :> wbytes st) s = keccak_f1600 (Sf:1600 word)` then NO_TAC else
      MAP_EVERY (fun k ->
        let c = MATCH_MP READ_MEMORY_BYTES128_OF_WBYTES (CONJ wth (ARITH_RULE(mk_binop `(<):num->num->bool` (mk_small_numeral k) `12`))) in
        let c = CONV_RULE(DEPTH_CONV NUM_MULT_CONV) (REWRITE_RULE[MULT_CLAUSES; WORD_ADD_0] c) in
        ASSUME_TAC c THEN ASSUME_TAC(norm c)) [0;1;2;3]) THEN
    YMM_GHOST_TAC s ["YMM0","y0"; "YMM1","y1"; "YMM2","y2"; "YMM3","y3"]) THEN
  ABBREV_TAC `KK = keccak_f1600 (Sf:1600 word)` THEN
  (* the copy *)
  HX_DRIVE_TAC exec [] (layout q.s6_fn + q.s6_exit) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPONGE_XMM_LOW]) THEN
  W(fun (asl,w) -> let s = hx_cur_state asl in
    SUBGOAL_THEN (subst [s,`s:x86state`] `read (memory :> bytes(out,64)) s = val(word_subword (KK:1600 word) (0,512):512 word)`)
      ASSUME_TAC THENL
     [MATCH_MP_TAC SPONGE_BYTES_OF_CHUNKS4 THEN REPEAT CONJ_TAC THEN
      FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> bytes128 a) s = x`) (concl th) then
        (MP_TAC th THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN NO_TAC) else NO_TAC);
      ALL_TAC]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[HXS64_DIGEST] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let HXS64_PROVE q = prove(HXS64_STMT q, HXS64_TAC q);;

(* the top level: facts for the region lemmas *)
let HX_NOV_SUB_RIGHT = prove
 (`!a n b k k'. k' <= k /\ nonoverlapping_modulo (2 EXP 64) (a,n) (b,k)
     ==> nonoverlapping_modulo (2 EXP 64) (a,n) (b,k') /\ nonoverlapping_modulo (2 EXP 64) (b,k') (a,n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN MATCH_MP_TAC TG_NOV_MONO THEN
    EXISTS_TAC `k:num` THEN ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN ASM_REWRITE_TAC[];
    MESON_TAC[NONOVERLAPPING_MODULO_SYM]]);;

(* nonoverlapping x (bq,fr') (both orientations) from (bq,fr) x, for all such *)
(* assumptions (one pass over the assumptions)                              *)
let HX_NOV_SHRINK_TAC fr fr' =
  let pat = subst [mk_small_numeral fr,`fr:num`] `nonoverlapping_modulo (2 EXP 64) (val (bq:int64),fr) x` in
  let bqv = `stackpointer:int64` in
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
    let c = concl th in
    match (try Some(term_match [] pat c) with _ -> None) with
      Some(_,i,_) when rev_assoc `bq:int64` i = bqv ->
        let x = rev_assoc `x:num#num` i in
        let th' = ONCE_REWRITE_RULE[NONOVERLAPPING_MODULO_SYM] th in
        let l = MP (SPECL [fst(dest_pair x); snd(dest_pair x); `val (stackpointer:int64)`; mk_small_numeral fr; mk_small_numeral fr'] HX_NOV_SUB_RIGHT)
                   (CONJ (ARITH_RULE(mk_binop `(<=):num->num->bool` (mk_small_numeral fr') (mk_small_numeral fr))) th') in
        MAP_EVERY ASSUME_TAC (CONJUNCTS l)
    | _ -> ALL_TAC) ths);;
