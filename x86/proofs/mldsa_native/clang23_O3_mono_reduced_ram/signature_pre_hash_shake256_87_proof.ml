(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing a message with a SHAKE256 pre-hash (HashML-DSA): the proof (see   *)
(* signature_pre_hash_shake256_87_spec.ml).                                  *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/signature_pre_hash_shake256_87_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/api_inline.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sponge_region.ml";;
needs "x86/proofs/utils/mldsa_native_api.ml";;
needs "x86/proofs/utils/mldsa_native_signing.ml";;

let SPHS87_EXEC =
  MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The frame. After REPEAT_GEN_AND_OFFSET_STACKPTR_TAC, stackpointer is the  *)
(* bottom of the 17045 bytes of stack below the return address, at           *)
(* stackpointer + 17045, with sk above it at + 17053; the code pushes RBP    *)
(* (the frame pointer), R15, R14, R13, R12 and RBX, from stackpointer +      *)
(* 17037 down to stackpointer + 16997, aligns RSP to 32 bytes, at bot +      *)
(* 16966 (see utils/mldsa_native_realign.ml), and reserves 480 bytes, with   *)
(* RSP = rsp0 = bot + 16486. The state of the inlined SHAKE256 is at rsp0 +  *)
(* 32 (the prefix is built there afterwards), its digest at rsp0 + 384, ctx  *)
(* is saved at rsp0 + 16 and rnd at rsp0 + 24. The inlined SHAKE256 is the   *)
(* lemma of inline_sponge_region.ml, from +0x2e to +0x2bb. The prefix, with  *)
(* 1, ctxlen, the context, the 11 bytes of the OID of SHAKE256 and the       *)
(* digest, is signed as the message by mldsa87_signature_internal with sk    *)
(* and ext = 0 pushed above its return address, at bot + 16462, its frame    *)
(* the 16462 bytes at bot. The events before a call are functions of the     *)
(* variables SPHS87_VARS, with bot, which REALIGN_UNBOT_TAC expands at the   *)
(* end.                                                                      *)
(* ------------------------------------------------------------------------- *)

let SPHS87_VARS =
  [`sig:int64`; `m:int64`; `mlen:num`; `ctx:int64`; `ctxlen:num`;
   `rnd:int64`; `sk:int64`; `skb:num->byte`; `M:num`; `C:num`; `RND:num`;
   `MU:num`; `mf:int64`; `mc:int64`; `pc:num`; `stackpointer:int64`;
   `returnaddress:int64`; `bot:int64`];;

let SPHS87_LE =
  SPECL [`12`; `ctxlen:num`; `64`] API_PREFIX_LENGTH_LE;;

let SPHS87_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   SPHS87_EXEC name
   (ilist @ [`pc:num`; `read RSP s`;
             `read (memory :> bytes64 (read RSP s)) s`])
   SPHS87_VARS n;;

(*** The events: by the context length (too long, empty or not), and by    ***)
(*** whether signing hits the last attempt                                 ***)

let SPHS87_TEMPLATE =
  `\(sig:int64) (m:int64) (mlen:num) (ctx:int64) (ctxlen:num) (rnd:int64)
    (sk:int64) (rho:num) (dcl:num->num#num#(num->int32)#(num->byte))
    (mf:int64) (mc:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
    if 255 < ctxlen
    then f_ev_0 sig m mlen ctx ctxlen rnd sk mf mc pc stackpointer returnaddress
    else if ctxlen = 0
    then (if (?n. FST(SND(dcl n)) = 24)
          then f_ev_1z sig m mlen ctx ctxlen rnd sk rho dcl mf mc pc stackpointer returnaddress
          else f_ev_2z sig m mlen ctx ctxlen rnd sk rho dcl mf mc pc stackpointer returnaddress)
    else (if (?n. FST(SND(dcl n)) = 24)
          then f_ev_1 sig m mlen ctx ctxlen rnd sk rho dcl mf mc pc stackpointer returnaddress
          else f_ev_2 sig m mlen ctx ctxlen rnd sk rho dcl mf mc pc stackpointer returnaddress)
    :(uarch_event)list`;;

let SPHS87_PRE =
  `num_of_bytelist(mld_domain_separation_prefix 12 (bytelist_of_num ctxlen C)
    (bytelist_of_num 64 (num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64))))`;;

(*** The frames of the lemma of the inlined SHAKE256 and the instructions  ***)
(*** that follow it in the callers' terms: word_sub of an offset of bot    ***)
(*** is not understood by the containment tactic                           ***)

let SPHS87_RW =
 [WORD_RULE `word_sub (word_sub (word_add (x:int64) (word 16486)) (word 8)) (word 288) = word_add x (word 16190)`;
  WORD_RULE `word_sub (word_add (x:int64) (word 16486)) (word 8) = word_add x (word 16478)`;
  WORD_RULE `word_sub (word_add (x:int64) (word 16478)) (word 288) = word_add x (word 16190)`];;

(*** The events so far as one list of concrete events followed by what the ***)
(*** callees did, which the tactics for calls expect when there are many   ***)
(*** events since the last callee                                          ***)

let SPHS87_COMPRESS_EVENTS =
  let is_cons t = (try fst(dest_const(rator(rator t))) = "CONS" with _ -> false) in
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if can (term_match [] `read events s = x`) c && is_cons (rand c) then
      let rec split t acc =
        if is_cons t then split (rand t) (rand(rator t)::acc) else (rev acc,t) in
      let heads,tl = split (rand c) [] in
      let ty = type_of(hd heads) in
      let lit = mk_list(heads,ty) in
      let app = mk_comb(mk_comb(mk_const("APPEND",[ty,`:A`]),lit),tl) in
      TRANS th (SYM(prove(mk_eq(app,rand c),REWRITE_TAC[APPEND])))
    else th);;

(*** The call of memset at step c; the state after it is c + 2            ***)

let SPHS87_MEMSET_TAC c =
  LIBC_PLT_TAC SPHS87_EXEC (layout "plt_memset") (layout "got_memset") c THEN
  LIBC_FULL_CALL_TAC "H_MEMSET" SPHS87_EXEC
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
    `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   (ref SPHS87_VARS) (c + 2);;

(*** From a935 at step t: the zeroing of the prefix and the return        ***)

let SPHS87_T_STEPS_TAC t =
  X86_STEPS_TAC SPHS87_EXEC ((t + 1)--(t + 5)) THEN
  SPHS87_MEMSET_TAC (t + 5) THEN
  X86_STEPS_TAC SPHS87_EXEC ((t + 8)--(t + 28));;

(*** From a923 at step c: the zeroing of the signature, then a935         ***)

let SPHS87_Z_STEPS_TAC c =
  X86_STEPS_TAC SPHS87_EXEC ((c + 1)--(c + 4)) THEN
  SPHS87_MEMSET_TAC (c + 4) THEN
  API_MEMSET_BYTES_TAC THEN
  X86_STEPS_TAC SPHS87_EXEC ((c + 7)--(c + 7)) THEN
  SPHS87_T_STEPS_TAC (c + 7);;

(*** The end of a path, and the events ***)

let SPHS87_FINAL_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[API_SIGN_DISTINCT] THEN
  REPEAT CONJ_TAC THEN TRY(API_RET_TAC THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC SIGN_BYTES8_ZERO THEN FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
  ABBREV_TAC `rho = mld_sk_rho skb` THEN
  ABBREV_TAC `dcl = mld_sign_declass_87 skb MU RND` THEN
  REALIGN_UNBOT_TAC THEN API_EMPTY_REGIONS_TAC THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* The digest as four chunks of 128 bits, the numbers that the code loads    *)
(* from rsp0 + 384 (the simulator needs them as such), and the normal form   *)
(* of the numbers in the chunks.                                             *)
(* ------------------------------------------------------------------------- *)

let SPHS87_CHUNKS =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes (word_add bot (word 16870),64)) s = x`) (concl th) then
      MAP_EVERY (fun t ->
        let le = ARITH_RULE(mk_binop `(<=):num->num->bool`
                  (mk_binop `(+):num->num->num` (mk_binop `(*):num->num->num` `16` (mk_small_numeral t)) `16`) `64`) in
        let f = SPONGE_NUMRED(MATCH_MP READ_MEMORY_BYTES128_OF_NUM (CONJ th le)) in
        ASSUME_TAC(SPONGE_NORMADDR f)) [0;1;2;3]
    else NO_TAC);;

let SPHS87_NORMC =
  REWRITE_RULE[DIV_1] o CONV_RULE(REDEPTH_CONV(NUM_MULT_CONV ORELSEC NUM_EXP_CONV)) o REWRITE_RULE[DIV_1];;

let SPHS87_CHUNKS_N = SPHS87_NORMC API_BYTES64_OF_CHUNKS;;

(*** The addresses of the pieces of the prefix as the simulator has them,  ***)
(*** with ctxlen not a numeral                                             ***)

let SPHS87_E = map WORD_RULE
 [`word_add (word_add (bot:int64) (word 16518)) (word 1) = word_add bot (word 16519)`;
  `word_add (word_add (bot:int64) (word 16518)) (word 2) = word_add bot (word 16520)`;
  `word_add (word_add (bot:int64) (word 16518)) (word (2 + ctxlen)) = word_add bot (word (16486 + 1 * ctxlen + 34))`;
  `word_add (word_add (bot:int64) (word (16486 + 1 * ctxlen + 34))) (word 7) = word_add bot (word (16486 + 1 * ctxlen + 41))`;
  `word_add (word_add (bot:int64) (word 16518)) (word (2 + ctxlen + 11)) = word_add bot (word (16486 + 1 * ctxlen + 45))`;
  `word_add (word_add (bot:int64) (word (16486 + 1 * ctxlen + 45))) (word 16) = word_add bot (word (16486 + 1 * ctxlen + 61))`;
  `word_add (word_add (bot:int64) (word (16486 + 1 * ctxlen + 45))) (word 32) = word_add bot (word (16486 + 1 * ctxlen + 77))`;
  `word_add (word_add (bot:int64) (word (16486 + 1 * ctxlen + 45))) (word 48) = word_add bot (word (16486 + 1 * ctxlen + 93))`];;

(* ------------------------------------------------------------------------- *)
(* From the label a8a3 at step j, with the bytes 1 and ctxlen and the        *)
(* context in the prefix buffer at rsp0 + 32: the OID and the digest are     *)
(* stored after the context, the prefix is signed, and the buffers are       *)
(* zeroed. p3 proves the context bytes of the buffer, and restore puts back  *)
(* the case facts that the simulator must not use before the end.            *)
(* ------------------------------------------------------------------------- *)

let SPHS87_JOIN_TAC j p3 restore =
  let sn k = mk_var("s"^string_of_int k,`:x86state`) in
  let sj = sn j and s21 = sn (j + 21) in
  let pat k s = parse_term(Printf.sprintf s k) in
  let ghost = YMM_GHOST_TAC sj ["YMM0","y0"; "YMM1","y1"; "YMM2","y2"; "YMM3","y3"] in
  SPHS87_CHUNKS THEN ghost THEN
  X86_STEPS_TAC SPHS87_EXEC ((j + 1)--(j + 2)) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] (pat (j + 2) "read (memory :> bytes64 a) s%d = word 244603165765273862")) (concl th)
    then ASSUME_TAC(MATCH_MP API_BYTES7_OF_BYTES64 (CONJ th (ARITH_RULE `244603165765273862 < 2 EXP 64`)))
    else NO_TAC) THEN
  X86_STEPS_TAC SPHS87_EXEC ((j + 3)--(j + 21)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPONGE_XMM_LOW]) THEN
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read (memory :> bytes128 a) s = word x`) (concl th) then SPHS87_NORMC th else th) THEN
  (*** the premises of API_HASH_PREFIX_BYTES ***)
  SUBGOAL_THEN (pat (j + 21) "read (memory :> bytes8 (word_add (word_add bot (word 16518)) (word 1))) s%d = word ctxlen") ASSUME_TAC THENL
   [REWRITE_TAC[el 0 SPHS87_E] THEN
    FIRST_ASSUM(fun th -> if can (term_match [] (pat (j + 21) "read (memory :> bytes8 (word_add bot (word 16519))) s%d = x")) (concl th) then
       MP_TAC th THEN ASM_REWRITE_TAC[API_WORD_MOD_256] THEN NO_TAC else NO_TAC);
    ALL_TAC] THEN
  SUBGOAL_THEN (pat (j + 21) "read (memory :> bytes(word_add (word_add bot (word 16518)) (word 2),ctxlen)) s%d = C") ASSUME_TAC THENL
   [p3 (j + 21); ALL_TAC] THEN
  SUBGOAL_THEN (pat (j + 21) "read (memory :> bytes(word_add (word_add bot (word 16518)) (word (2 + ctxlen)),11)) s%d = num_of_bytelist(mld_prehash_oid 12)") ASSUME_TAC THENL
   [REWRITE_TAC[el 2 SPHS87_E] THEN MATCH_MP_TAC API_OID12_BYTES THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; REWRITE_TAC[el 3 SPHS87_E] THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN (pat (j + 21) "read (memory :> bytes(word_add (word_add bot (word 16518)) (word (2 + ctxlen + 11)),64)) s%d = num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64)") ASSUME_TAC THENL
   [REWRITE_TAC[el 4 SPHS87_E] THEN MATCH_MP_TAC SPHS87_CHUNKS_N THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM(fun th -> if can (term_match [] (pat (j + 21) "read (memory :> bytes (word_add bot (word 16870),64)) s%d = x")) (concl th) then
        MP_TAC(MATCH_MP API_READ_BYTES_BOUND th) THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN NO_TAC else NO_TAC);
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[el 5 SPHS87_E] THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[el 6 SPHS87_E] THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[el 7 SPHS87_E] THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [s21; `word_add bot (word 16518):int64`; `ctxlen:num`; `C:num`;
                `num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64)`] API_HASH_PREFIX_BYTES) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `2 + ctxlen + 11 + 64 = ctxlen + 77`] THEN DISCH_TAC THEN
  (*** the length of the prefix as the code computes it, and as the callee has it ***)
  SUBGOAL_THEN `mld_domain_separation_prefix_length 12 ctxlen 64 = ctxlen + 77` ASSUME_TAC THENL
   [REWRITE_TAC[API_PREFIX_LENGTH_SHAKE256] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun peq ->
    RULE_ASSUM_TAC(fun th ->
      if can (term_match [] `read (memory :> bytes (a, ctxlen + 77)) s = x`) (concl th) ||
         can (term_match [] (pat (j + 21) "read RDX s%d = x")) (concl th)
      then REWRITE_RULE[GSYM WORD_ADD; GSYM peq] th else th)) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    concl th = `mld_domain_separation_prefix_length 12 ctxlen 64 = ctxlen + 77`)) THEN
  (*** the signing of the prefix ***)
  MAP_EVERY (fun r -> API_DRIVER_TAC
    (mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,r),
             mk_pair(`word_add bot (word 16518):int64`,
                     `mld_domain_separation_prefix_length 12 ctxlen 64`)))
    SPHS87_LE)
   [`word_add bot (word 16478):int64,8`; `word_add bot (word 16470):int64,8`;
    `word_add bot (word 16462):int64,8`; `bot:int64,16462`;
    `sig:int64,4627`] THEN
  API_NULL_TAC [`sig:int64`,`4627`; `bot:int64`,`16462`] THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] (pat (j + 21) "read (memory :> bytes64 a) s%d = word 0")) (concl th)
    then ASSUME_TAC(CONV_RULE(RAND_CONV WORD_REDUCE_CONV) (MATCH_MP SIGN_BYTES32_OF_BYTES64 th))
    else NO_TAC) THEN
  SUBGOAL_THEN `mld_domain_separation_prefix_length 12 ctxlen 64 < 2 EXP 64` ASSUME_TAC THENL
   [MP_TAC SPHS87_LE THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word (mld_domain_separation_prefix_length 12 ctxlen 64):int64) =
                mld_domain_separation_prefix_length 12 ctxlen 64` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN MP_TAC SPHS87_LE THEN ARITH_TAC; ALL_TAC] THEN
  ASSUME_TAC(ARITH_RULE `0 < 2 EXP 64`) THEN
  X86_STEPS_TAC SPHS87_EXEC ((j + 22)--(j + 22)) THEN
  SPHS87_COMPRESS_EVENTS THEN
  SPHS87_CALL_TAC "H_INTERNAL"
   [`read RDI s`; `read RSI s`; `mld_domain_separation_prefix_length 12 ctxlen 64`; `read RCX s`; `0`;
    `read R9 s`; `sk:int64`; `word 0:int32`; `skb:num->byte`;
    SPHS87_PRE; `0`; `RND:num`; `MU:num`] (j + 23) THEN
  API_WIDEN_TAC
   [prove(mk_comb(mk_comb(`contained:int64#num->int64#num->bool`,
                          mk_pair(`word_add bot (word 16518):int64`,
                                  `mld_domain_separation_prefix_length 12 ctxlen 64`)),
                  `word_add bot (word 16518):int64,332`),
          REWRITE_TAC[contained; CONTAINED_MODULO_REFL; API_PREFIX_LENGTH_LE])] THEN
  X86_STEPS_TAC SPHS87_EXEC ((j + 24)--(j + 26)) THEN
  ASM_CASES_TAC `mld_sign_ok_87 skb MU RND` THEN
  API_USE_CASE_TAC `mld_sign_ok_87 skb MU RND` [] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[API_SIGN_OK_DECLASS_87] o
    check (fun th -> concl th = `mld_sign_ok_87 skb MU RND` ||
                     concl th = `~mld_sign_ok_87 skb MU RND`)) THENL
   [X86_STEPS_TAC SPHS87_EXEC ((j + 27)--(j + 27)) THEN
    SPHS87_T_STEPS_TAC (j + 27) THEN restore THEN SPHS87_FINAL_TAC;
    ASSUME_TAC(GEN `t:num` (MP (SPECL [`skb:num->byte`; `MU:num`;
      `RND:num`; `t:num`] (CONJUNCT2(CONJUNCT2 API_SIGN_SIG_FAIL)))
      (ASSUME `~mld_sign_ok_87 skb MU RND`))) THEN
    X86_STEPS_TAC SPHS87_EXEC ((j + 27)--(j + 27)) THEN
    SPHS87_Z_STEPS_TAC (j + 27) THEN restore THEN SPHS87_FINAL_TAC];;

(*** 0 < ctxlen <= 255: the context is copied with memcpy ***)

let SPHS87_CALL_REGION_TAC =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc SPHS87_EXEC
   "H_REGION" [`m:int64`; `mlen:num`; `M:num`; `read RSP s`; `pc:num`]
   SPHS87_VARS 16 THEN
  RULE_ASSUM_TAC(REWRITE_RULE SPHS87_RW);;

let SPHS87_COPY_TAC =
  SUBGOAL_THEN `~(word ctxlen:int64 = word 0)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN ASM_REWRITE_TAC[VAL_WORD_0]; ALL_TAC] THEN
  API_PC_TAC [`word ctxlen:int64 = word 0`] THEN
  X86_STEPS_TAC SPHS87_EXEC (25--28) THEN
  LIBC_PLT_TAC SPHS87_EXEC (layout "plt_memcpy") (layout "got_memcpy") 28 THEN
  LIBC_FULL_CALL_TAC "H_MEMCPY" SPHS87_EXEC
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
    `C:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   (ref SPHS87_VARS) 30 THEN
  SPHS87_JOIN_TAC 30
   (fun n -> REWRITE_TAC[el 1 SPHS87_E] THEN FIRST_ASSUM ACCEPT_TAC) ALL_TAC;;

(*** ctxlen = 0: nothing to copy; ctxlen and C are not rewritten by the    ***)
(*** simulation, which has them as ctxlen <= 0 and C <= 0 until the end    ***)

let SPHS87_ZERO_TAC =
  SUBGOAL_THEN `C <= 0` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> bytes(ctx,ctxlen)) s24 = C`) (concl th) then
      MP_TAC(REWRITE_RULE[ASSUME `ctxlen = 0`; READ_MEMORY_BYTES_TRIVIAL] th) THEN ARITH_TAC else NO_TAC);
    ALL_TAC] THEN
  SUBGOAL_THEN `word ctxlen:int64 = word 0` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ctxlen <= 0` ASSUME_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `ctxlen = 0`)) THEN
  API_PC_TAC [`word ctxlen:int64 = word 0`] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `word ctxlen:int64 = word 0`)) THEN
  SPHS87_JOIN_TAC 24
   (fun n ->
      SUBGOAL_THEN `ctxlen = 0` SUBST1_TAC THENL [UNDISCH_TAC `ctxlen <= 0` THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `C = 0` SUBST1_TAC THENL [UNDISCH_TAC `C <= 0` THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[READ_MEMORY_BYTES_TRIVIAL])
   (FIRST_ASSUM(fun th -> if concl th = `ctxlen <= 0` then
      ASSUME_TAC(MP (ARITH_RULE `ctxlen <= 0 ==> ctxlen = 0`) th) else NO_TAC));;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety, by cases on whether the     *)
(* context is too long, empty or not, and on whether signing succeeds.       *)
(* ------------------------------------------------------------------------- *)

let SPHS87_REGION = PROVE_SPONGE_FULL "mldsa87_signature_pre_hash_shake256" "R14";;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mcb = CONJ_PAIR th in
    API_ASSUME_CALLEE_TAC
     (MATCH_MP
       MLDSA_NATIVE_SIGNATURE_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
       th) "H_INTERNAL" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] ms)
     "H_MEMSET" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memcpy_full_contract] mcb)
     "H_MEMCPY" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 SPHS87_REGION)
     "H_REGION") THEN
  CONCRETIZE_F_EVENTS_TAC SPHS87_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SPHS87_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = v)))
   [`PH:num`; mk_var("PRE'",`:num`)] THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `MU:num`)) THEN
  REALIGN_TAC 16997 THEN REALIGN_FRAME_TAC 17045 16997 THEN
  REALIGN_NONOV_TAC 16966
   [`sig:int64,4627`; `m:int64,mlen:num`; `ctx:int64,ctxlen:num`;
    `rnd:int64,32`; `sk:int64,4896`; `word pc:int64,libmldsa_size`;
    `word(pc + got_memset):int64,8`; `word(pc + got_memcpy):int64,8`;
    `ea:int64,el:num`;
    `word_add stackpointer (word 16997):int64,48`;
    `word_add stackpointer (word 17045):int64,16`] THEN
  REALIGN_ALIGNED_TAC [16486] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15` THEN
  FULL_INIT_TAC THEN
  X86_STEPS_TAC SPHS87_EXEC (1--8) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC SPHS87_EXEC (9--15) THEN
  SPHS87_CALL_REGION_TAC THEN
  X86_STEPS_TAC SPHS87_EXEC (17--19) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP API_JA_255 (ASSUME `ctxlen < 2 EXP 64`);
                              NOT_LE]) THEN
  ASM_CASES_TAC `255 < ctxlen` THEN
  API_USE_CASE_TAC `255 < ctxlen` [ADD_EQ_0; ARITH_EQ] THENL
   [SPHS87_Z_STEPS_TAC 19 THEN SPHS87_FINAL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ctxlen <= 255` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM NOT_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `2 + ctxlen < 2 EXP 64` ASSUME_TAC THENL
   [UNDISCH_TAC `ctxlen <= 255` THEN ARITH_TAC; ALL_TAC] THEN
  API_MP_TAC `ctxlen <= 255` THEN
  X86_STEPS_TAC SPHS87_EXEC (20--24) THEN
  SUBGOAL_THEN `val(word ctxlen:int64) = ctxlen` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `ctxlen = 0` THENL [SPHS87_ZERO_TAC; SPHS87_COPY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  API_SIGN_CORRECT_TAC
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  API_SIGN_SAFE_TAC
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;
