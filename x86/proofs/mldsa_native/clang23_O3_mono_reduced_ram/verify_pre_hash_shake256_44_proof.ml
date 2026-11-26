(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verifying a signature of a message with a SHAKE256 pre-hash (HashML-DSA): *)
(* the proof (see verify_pre_hash_shake256_44_spec.ml).                      *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/verify_pre_hash_shake256_44_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/api_inline.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sponge_region.ml";;
needs "x86/proofs/utils/mldsa_native_api.ml";;
needs "x86/proofs/utils/mldsa_native_verify.ml";;

let VPHS44_EXEC =
  MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The frame. After REPEAT_GEN_AND_OFFSET_STACKPTR_TAC, stackpointer is the  *)
(* bottom of the 11516 bytes of stack below the return address, at           *)
(* stackpointer + 11516; the code pushes RBP (the frame pointer), R15, R14,  *)
(* R13, R12 and RBX, from stackpointer + 11508 down to stackpointer + 11468, *)
(* aligns RSP to 32 bytes, at bot + 11437 (see                               *)
(* utils/mldsa_native_realign.ml), and reserves 480 bytes, with RSP = rsp0 = *)
(* bot + 10957, ext, the seventh argument of mldsa44_verify_internal, at     *)
(* rsp0. The state of the inlined SHAKE256 is at rsp0 + 32 (the prefix is    *)
(* built there afterwards), its digest at rsp0 + 384, ctx is saved at rsp0 + *)
(* 16 and pk at rsp0 + 24. The inlined SHAKE256 is the lemma of              *)
(* inline_sponge_region.ml, from +0x2e to +0x2bb. The prefix, with 1,        *)
(* ctxlen, the context, the 11 bytes of the OID of SHAKE256 and the digest,  *)
(* is the message that mldsa44_verify_internal verifies, with its return     *)
(* address at bot + 10949 and its frame the 10949 bytes at bot. The events   *)
(* before a call are functions of the variables VPHS44_VARS, with bot, which *)
(* REALIGN_UNBOT_TAC expands at the end.                                     *)
(* ------------------------------------------------------------------------- *)

let VPHS44_VARS =
  [`sig:int64`; `m:int64`; `mlen:num`; `ctx:int64`; `ctxlen:num`;
   `pk:int64`; `sigb:num->byte`; `pkb:num->byte`; `M:num`; `C:num`;
   `mf:int64`; `mc:int64`; `pc:num`; `stackpointer:int64`;
   `returnaddress:int64`; `bot:int64`];;

let VPHS44_LE =
  SPECL [`12`; `ctxlen:num`; `64`] API_PREFIX_LENGTH_LE;;

let VPHS44_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   VPHS44_EXEC name
   (ilist @ [`pc:num`; `read RSP s`;
             `read (memory :> bytes64 (read RSP s)) s`])
   VPHS44_VARS n;;

(*** The events: by the context length (too long, empty or not) ***)

let VPHS44_TEMPLATE =
  `\(sig:int64) (m:int64) (mlen:num) (ctx:int64) (ctxlen:num) (pk:int64)
    (sigb:num->byte) (pkb:num->byte) (M:num) (C:num) (mf:int64) (mc:int64)
    (pc:num) (stackpointer:int64) (returnaddress:int64).
    if 255 < ctxlen
    then f_ev_rej sig m mlen ctx ctxlen pk sigb pkb M C mf mc pc stackpointer
          returnaddress
    else if ctxlen = 0
    then f_ev_nul sig m mlen ctx ctxlen pk sigb pkb M C mf mc pc stackpointer
          returnaddress
    else f_ev_acc sig m mlen ctx ctxlen pk sigb pkb M C mf mc pc stackpointer
          returnaddress
    :(uarch_event)list`;;

let VPHS44_PRE =
  `num_of_bytelist(mld_domain_separation_prefix 12 (bytelist_of_num ctxlen C)
    (bytelist_of_num 64 (num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64))))`;;

(*** The frames of the lemma of the inlined SHAKE256 in the callers' terms: ***)
(*** word_sub of an offset of bot is not understood by the containment      ***)
(*** tactic                                                                 ***)

let VPHS44_RW =
 [WORD_RULE `word_sub (word_sub (word_add (x:int64) (word 10957)) (word 8)) (word 288) = word_add x (word 10661)`;
  WORD_RULE `word_sub (word_add (x:int64) (word 10957)) (word 8) = word_add x (word 10949)`;
  WORD_RULE `word_sub (word_add (x:int64) (word 10949)) (word 288) = word_add x (word 10661)`];;

(*** The events so far as one list of concrete events followed by what the ***)
(*** callees did, which the tactics for calls expect when there are many   ***)
(*** events since the last callee                                          ***)

let VPHS44_COMPRESS_EVENTS =
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

let VPHS44_MEMSET_TAC c =
  LIBC_PLT_TAC VPHS44_EXEC (layout "plt_memset") (layout "got_memset") c THEN
  LIBC_FULL_CALL_TAC "H_MEMSET" VPHS44_EXEC
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
    `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   (ref VPHS44_VARS) (c + 2);;

(*** From ad85 at step t: the zeroing of the prefix and the return        ***)

let VPHS44_T_STEPS_TAC t =
  X86_STEPS_TAC VPHS44_EXEC ((t + 1)--(t + 5)) THEN
  VPHS44_MEMSET_TAC (t + 5) THEN
  X86_STEPS_TAC VPHS44_EXEC ((t + 8)--(t + 28));;

(*** The end of a path, and the events ***)

let VPHS44_FINAL_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(VERIF_RET_TAC THEN NO_TAC) THEN
  REALIGN_UNBOT_TAC THEN VERIF_EMPTY_REGIONS_TAC THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* The digest as four chunks of 128 bits, the numbers that the code loads    *)
(* from rsp0 + 384 (the simulator needs them as such), and the normal form   *)
(* of the numbers in the chunks.                                             *)
(* ------------------------------------------------------------------------- *)

let VPHS44_CHUNKS =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes (word_add bot (word 11341),64)) s = x`) (concl th) then
      MAP_EVERY (fun t ->
        let le = ARITH_RULE(mk_binop `(<=):num->num->bool`
                  (mk_binop `(+):num->num->num` (mk_binop `(*):num->num->num` `16` (mk_small_numeral t)) `16`) `64`) in
        let f = SPONGE_NUMRED(MATCH_MP READ_MEMORY_BYTES128_OF_NUM (CONJ th le)) in
        ASSUME_TAC(SPONGE_NORMADDR f)) [0;1;2;3]
    else NO_TAC);;

let VPHS44_NORMC =
  REWRITE_RULE[DIV_1] o CONV_RULE(REDEPTH_CONV(NUM_MULT_CONV ORELSEC NUM_EXP_CONV)) o REWRITE_RULE[DIV_1];;

let VPHS44_CHUNKS_N = VPHS44_NORMC API_BYTES64_OF_CHUNKS;;

(*** The addresses of the pieces of the prefix as the simulator has them,  ***)
(*** with ctxlen not a numeral                                             ***)

let VPHS44_E = map WORD_RULE
 [`word_add (word_add (bot:int64) (word 10989)) (word 1) = word_add bot (word 10990)`;
  `word_add (word_add (bot:int64) (word 10989)) (word 2) = word_add bot (word 10991)`;
  `word_add (word_add (bot:int64) (word 10989)) (word (2 + ctxlen)) = word_add bot (word (10957 + 1 * ctxlen + 34))`;
  `word_add (word_add (bot:int64) (word (10957 + 1 * ctxlen + 34))) (word 7) = word_add bot (word (10957 + 1 * ctxlen + 41))`;
  `word_add (word_add (bot:int64) (word 10989)) (word (2 + ctxlen + 11)) = word_add bot (word (10957 + 1 * ctxlen + 45))`;
  `word_add (word_add (bot:int64) (word (10957 + 1 * ctxlen + 45))) (word 16) = word_add bot (word (10957 + 1 * ctxlen + 61))`;
  `word_add (word_add (bot:int64) (word (10957 + 1 * ctxlen + 45))) (word 32) = word_add bot (word (10957 + 1 * ctxlen + 77))`;
  `word_add (word_add (bot:int64) (word (10957 + 1 * ctxlen + 45))) (word 48) = word_add bot (word (10957 + 1 * ctxlen + 93))`];;

(* ------------------------------------------------------------------------- *)
(* From the label ad0e at step j, with the bytes 1 and ctxlen and the        *)
(* context in the prefix buffer at rsp0 + 32: the OID and the digest are     *)
(* stored after the context, the prefix is verified as the message, and the  *)
(* buffers are zeroed. p3 proves the context bytes of the buffer, and        *)
(* restore puts back the case facts that the simulator must not use before   *)
(* the end.                                                                  *)
(* ------------------------------------------------------------------------- *)

let VPHS44_JOIN_TAC j p3 restore =
  let sn k = mk_var("s"^string_of_int k,`:x86state`) in
  let sj = sn j and sc = sn (j + 19) in
  let pat k s = parse_term(Printf.sprintf s k) in
  let ghost = YMM_GHOST_TAC sj ["YMM0","y0"; "YMM1","y1"; "YMM2","y2"; "YMM3","y3"] in
  VPHS44_CHUNKS THEN ghost THEN
  X86_STEPS_TAC VPHS44_EXEC ((j + 1)--(j + 2)) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] (pat (j + 2) "read (memory :> bytes64 a) s%d = word 244603165765273862")) (concl th)
    then ASSUME_TAC(MATCH_MP API_BYTES7_OF_BYTES64 (CONJ th (ARITH_RULE `244603165765273862 < 2 EXP 64`)))
    else NO_TAC) THEN
  X86_STEPS_TAC VPHS44_EXEC ((j + 3)--(j + 19)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPONGE_XMM_LOW]) THEN
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read (memory :> bytes128 a) s = word x`) (concl th) then VPHS44_NORMC th else th) THEN
  (*** the premises of API_HASH_PREFIX_BYTES ***)
  SUBGOAL_THEN (pat (j + 19) "read (memory :> bytes8 (word_add (word_add bot (word 10989)) (word 1))) s%d = word ctxlen") ASSUME_TAC THENL
   [REWRITE_TAC[el 0 VPHS44_E] THEN
    FIRST_ASSUM(fun th -> if can (term_match [] (pat (j + 19) "read (memory :> bytes8 (word_add bot (word 10990))) s%d = x")) (concl th) then
       MP_TAC th THEN ASM_REWRITE_TAC[API_WORD_MOD_256] THEN NO_TAC else NO_TAC);
    ALL_TAC] THEN
  SUBGOAL_THEN (pat (j + 19) "read (memory :> bytes(word_add (word_add bot (word 10989)) (word 2),ctxlen)) s%d = C") ASSUME_TAC THENL
   [p3 (j + 19); ALL_TAC] THEN
  SUBGOAL_THEN (pat (j + 19) "read (memory :> bytes(word_add (word_add bot (word 10989)) (word (2 + ctxlen)),11)) s%d = num_of_bytelist(mld_prehash_oid 12)") ASSUME_TAC THENL
   [REWRITE_TAC[el 2 VPHS44_E] THEN MATCH_MP_TAC API_OID12_BYTES THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; REWRITE_TAC[el 3 VPHS44_E] THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN (pat (j + 19) "read (memory :> bytes(word_add (word_add bot (word 10989)) (word (2 + ctxlen + 11)),64)) s%d = num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64)") ASSUME_TAC THENL
   [REWRITE_TAC[el 4 VPHS44_E] THEN MATCH_MP_TAC VPHS44_CHUNKS_N THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM(fun th -> if can (term_match [] (pat (j + 19) "read (memory :> bytes (word_add bot (word 11341),64)) s%d = x")) (concl th) then
        MP_TAC(MATCH_MP API_READ_BYTES_BOUND th) THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN NO_TAC else NO_TAC);
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[el 5 VPHS44_E] THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[el 6 VPHS44_E] THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[el 7 VPHS44_E] THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [sc; `word_add bot (word 10989):int64`; `ctxlen:num`; `C:num`;
                `num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64)`] API_HASH_PREFIX_BYTES) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `2 + ctxlen + 11 + 64 = ctxlen + 77`] THEN DISCH_TAC THEN
  (*** the length of the prefix as the code computes it, and as the callee has it ***)
  SUBGOAL_THEN `mld_domain_separation_prefix_length 12 ctxlen 64 = ctxlen + 77` ASSUME_TAC THENL
   [REWRITE_TAC[API_PREFIX_LENGTH_SHAKE256] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun peq ->
    RULE_ASSUM_TAC(fun th ->
      if can (term_match [] `read (memory :> bytes (a, ctxlen + 77)) s = x`) (concl th) ||
         can (term_match [] (pat (j + 19) "read RDX s%d = x")) (concl th)
      then REWRITE_RULE[GSYM WORD_ADD; GSYM peq] th else th)) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    concl th = `mld_domain_separation_prefix_length 12 ctxlen 64 = ctxlen + 77`)) THEN
  (*** the verification of the prefix ***)
  MAP_EVERY (fun r -> API_DRIVER_TAC
    (mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,r),
             mk_pair(`word_add bot (word 10989):int64`,
                     `mld_domain_separation_prefix_length 12 ctxlen 64`)))
    VPHS44_LE)
   [`word_add bot (word 10957):int64,8`; `word_add bot (word 10949):int64,8`;
    `bot:int64,10949`] THEN
  VERIF_NULL_TAC [`bot:int64`,`10949`] THEN
  SUBGOAL_THEN `mld_domain_separation_prefix_length 12 ctxlen 64 < 2 EXP 64` ASSUME_TAC THENL
   [MP_TAC VPHS44_LE THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word (mld_domain_separation_prefix_length 12 ctxlen 64):int64) =
                mld_domain_separation_prefix_length 12 ctxlen 64` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN MP_TAC VPHS44_LE THEN ARITH_TAC; ALL_TAC] THEN
  ASSUME_TAC(ARITH_RULE `0 < 2 EXP 64`) THEN
  X86_STEPS_TAC VPHS44_EXEC ((j + 20)--(j + 20)) THEN
  VPHS44_COMPRESS_EVENTS THEN
  VPHS44_CALL_TAC "H_INTERNAL"
   [`read RDI s`; `read RSI s`; `mld_domain_separation_prefix_length 12 ctxlen 64`; `read RCX s`; `0`;
    `read R9 s`; `word 0:int32`; `sigb:num->byte`; `pkb:num->byte`;
    VPHS44_PRE; `0`] (j + 21) THEN
  VERIF_WIDEN_TAC
   [prove(mk_comb(mk_comb(`contained:int64#num->int64#num->bool`,
                          mk_pair(`word_add bot (word 10989):int64`,
                                  `mld_domain_separation_prefix_length 12 ctxlen 64`)),
                  `word_add bot (word 10989):int64,332`),
          REWRITE_TAC[contained; CONTAINED_MODULO_REFL; API_PREFIX_LENGTH_LE])] THEN
  X86_STEPS_TAC VPHS44_EXEC ((j + 22)--(j + 22)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[API_PREFIX_LENGTH_SHAKE256; ASSUME `~(255 < ctxlen)`]) THEN
  VPHS44_T_STEPS_TAC (j + 22) THEN restore THEN VPHS44_FINAL_TAC;;

(*** 0 < ctxlen <= 255: the context is copied with memcpy ***)

let VPHS44_COPY_TAC =
  SUBGOAL_THEN `~(word ctxlen:int64 = word 0)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN ASM_REWRITE_TAC[VAL_WORD_0]; ALL_TAC] THEN
  API_PC_TAC [`word ctxlen:int64 = word 0`] THEN
  X86_STEPS_TAC VPHS44_EXEC (24--27) THEN
  LIBC_PLT_TAC VPHS44_EXEC (layout "plt_memcpy") (layout "got_memcpy") 27 THEN
  LIBC_FULL_CALL_TAC "H_MEMCPY" VPHS44_EXEC
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
    `C:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   (ref VPHS44_VARS) 29 THEN
  VPHS44_JOIN_TAC 29
   (fun n -> REWRITE_TAC[el 1 VPHS44_E] THEN FIRST_ASSUM ACCEPT_TAC) ALL_TAC;;

(*** ctxlen = 0: nothing to copy; ctxlen and C are not rewritten by the    ***)
(*** simulation, which has them as ctxlen <= 0 and C <= 0 until the end    ***)

let VPHS44_ZERO_TAC =
  SUBGOAL_THEN `C <= 0` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> bytes(ctx,ctxlen)) s23 = C`) (concl th) then
      MP_TAC(REWRITE_RULE[ASSUME `ctxlen = 0`; READ_MEMORY_BYTES_TRIVIAL] th) THEN ARITH_TAC else NO_TAC);
    ALL_TAC] THEN
  SUBGOAL_THEN `word ctxlen:int64 = word 0` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ctxlen <= 0` ASSUME_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `ctxlen = 0`)) THEN
  API_PC_TAC [`word ctxlen:int64 = word 0`] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `word ctxlen:int64 = word 0`)) THEN
  VPHS44_JOIN_TAC 23
   (fun n ->
      SUBGOAL_THEN `ctxlen = 0` SUBST1_TAC THENL [UNDISCH_TAC `ctxlen <= 0` THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `C = 0` SUBST1_TAC THENL [UNDISCH_TAC `C <= 0` THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[READ_MEMORY_BYTES_TRIVIAL])
   (FIRST_ASSUM(fun th -> if concl th = `ctxlen <= 0` then
      ASSUME_TAC(MP (ARITH_RULE `ctxlen <= 0 ==> ctxlen = 0`) th) else NO_TAC));;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety, by cases on whether the     *)
(* context is too long and whether it is empty.                              *)
(* ------------------------------------------------------------------------- *)

let VPHS44_REGION = PROVE_SPONGE_FULL "mldsa44_verify_pre_hash_shake256" "RBX";;

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mcb = CONJ_PAIR th in
    VERIF_ASSUME_CALLEE_TAC
     (MATCH_MP
       MLDSA_NATIVE_VERIFY_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
       th) "H_INTERNAL" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] ms)
     "H_MEMSET" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memcpy_full_contract] mcb)
     "H_MEMCPY" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 VPHS44_REGION)
     "H_REGION") THEN
  CONCRETIZE_F_EVENTS_TAC VPHS44_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; NONOVERLAPPING_CLAUSES; fst VPHS44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = v)))
   [`PH:num`; mk_var("PRE'",`:num`)] THEN
  REALIGN_TAC 11468 THEN REALIGN_FRAME_TAC 11516 11468 THEN
  REALIGN_NONOV_TAC 11437
   [`sig:int64,2420`; `m:int64,mlen:num`; `ctx:int64,ctxlen:num`;
    `pk:int64,1312`; `word pc:int64,libmldsa_size`;
    `word(pc + got_memset):int64,8`; `word(pc + got_memcpy):int64,8`;
    `ea:int64,el:num`;
    `word_add stackpointer (word 11468):int64,48`;
    `word_add stackpointer (word 11516):int64,8`] THEN
  REALIGN_ALIGNED_TAC [10957] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15` THEN
  FULL_INIT_TAC THEN
  X86_STEPS_TAC VPHS44_EXEC (1--8) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC VPHS44_EXEC (9--15) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc VPHS44_EXEC
   "H_REGION" [`m:int64`; `mlen:num`; `M:num`; `read RSP s`; `pc:num`]
   VPHS44_VARS 16 THEN
  RULE_ASSUM_TAC(REWRITE_RULE VPHS44_RW) THEN
  X86_STEPS_TAC VPHS44_EXEC (17--19) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP API_JA_255 (ASSUME `ctxlen < 2 EXP 64`);
                              NOT_LE]) THEN
  ASM_CASES_TAC `255 < ctxlen` THEN
  VERIF_USE_CASE_TAC `255 < ctxlen` [ADD_EQ_0; ARITH_EQ] THENL
   [VPHS44_T_STEPS_TAC 19 THEN VPHS44_FINAL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ctxlen <= 255` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM NOT_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `2 + ctxlen < 2 EXP 64` ASSUME_TAC THENL
   [UNDISCH_TAC `ctxlen <= 255` THEN ARITH_TAC; ALL_TAC] THEN
  VERIF_MP_TAC `ctxlen <= 255` THEN
  X86_STEPS_TAC VPHS44_EXEC (20--23) THEN
  SUBGOAL_THEN `val(word ctxlen:int64) = ctxlen` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `ctxlen = 0` THENL [VPHS44_ZERO_TAC; VPHS44_COPY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;
