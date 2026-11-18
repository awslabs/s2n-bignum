(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform sampling of a polynomial mod q from a seed: the proof (see        *)
(* poly_uniform_spec.ml). As on AArch64, it follows the proof for            *)
(* mldsa_poly_uniform_4x for one polynomial, with the incremental SHAKE128   *)
(* functions: absorbing the seed into the zero state and finalizing give the *)
(* absorbed state of the 4-way functions (MLD_KECCAK_ABSORB_ONCE_SHORT), so  *)
(* that the bytes squeezed are those of mld_shake128_stream. The x86 code    *)
(* aligns its frame to 32 bytes with AND RSP,-32 after saving five           *)
(* registers, so that the context and the buffer are at fixed offsets from   *)
(* bot, the bottom of the aligned part of the frame (see                     *)
(* utils/mldsa_native_realign.ml).                                           *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/poly_uniform_spec.ml";;
needs "x86/proofs/utils/mldsa_native_sampling.ml";;
needs "x86/proofs/utils/mldsa_native_realign.ml";;

let POLY_UNIFORM_EXEC = MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The count of coefficients after t blocks after the first five, and the    *)
(* events: those to the end of the first sampling (p1), of the loop over the *)
(* k0 more blocks that are needed, k0 = mld_poly_uniform_nblocks of the      *)
(* stream, or of the branch round it if k0 = 0, and those of releasing the   *)
(* state, zeroing the buffer and returning (p3). The events before a call    *)
(* may depend on bot, which REALIGN_UNBOT_TAC removes before they are        *)
(* matched with the template at the end of each part                         *)
(* (POLY_UNIFORM_DISCHARGE_TAC).                                             *)
(* ------------------------------------------------------------------------- *)

let poly_uniform_count t =
  vsubst [t,`t:num`]
   `MIN 256 (LENGTH(mld_rej_uniform_list (mld_shake128_stream 34 M)
                                         (280 + 56 * t)))`;;

let poly_uniform_count0 =
  rhs(concl(REWRITE_CONV[MULT_CLAUSES; ADD_CLAUSES]
             (poly_uniform_count `0`)));;

let POLY_UNIFORM_DONE t =
  vsubst [t,`t:num`]
   `256 <= LENGTH(mld_rej_uniform_list (mld_shake128_stream 34 M)
                                       (280 + 56 * t))`;;

let POLY_UNIFORM_TEMPLATE =
  let args = [`a:int64`; `seed:int64`; `M:num`;
              `pc:num`; `stackpointer:int64`; `returnaddress:int64`] in
  let fty = itlist (fun a t -> mk_fun_ty (type_of a) t) args
                   `:(uarch_event)list` in
  let fv n = mk_var(n,fty) in
  let app n = list_mk_comb(fv n,args) in
  let k0 = `mld_poly_uniform_nblocks (mld_shake128_stream 34 M)` in
  let fl = list_mk_comb(mk_var("f_ev_loop",
             itlist (fun a t -> mk_fun_ty (type_of a) t) args
                    (mk_fun_ty `:num` `:(uarch_event)list`)),args) in
  let loop = mk_abs(`i:num`,mk_comb(fl,`i:num`)) in
  let ap = `APPEND:(uarch_event)list->(uarch_event)list->(uarch_event)list` in
  let enum = list_mk_comb(`ENUMERATEL:num->(num->(uarch_event)list)->
                                     (uarch_event)list`,[k0;loop]) in
  let mid = mk_cond(mk_eq(k0,`0`),app "f_ev_skip",
              list_mk_comb(ap,[app "f_ev_exit";
                list_mk_comb(ap,[enum; app "f_ev_enter"])])) in
  let body = list_mk_comb(ap,[app "f_ev_p3";
               list_mk_comb(ap,[mid; app "f_ev_p1"])]) in
  list_mk_abs(args,body);;

let POLY_UNIFORM_ALLOWED =
  [`pc:num`; `a:int64`; `seed:int64`; `M:num`;
   `stackpointer:int64`; `returnaddress:int64`; `bot:int64`; `i:num`;
   `c:num`;
   `f_ev_loop:int64->int64->num->num->int64->int64->
              num->(uarch_event)list`];;

let POLY_UNIFORM_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc POLY_UNIFORM_EXEC name
    (ilist @ [`pc:num`; `read RSP s`;
              `read (memory :> bytes64 (read RSP s)) s`])
    POLY_UNIFORM_ALLOWED n;;

let POLY_UNIFORM_DISCHARGE_TAC =
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* The facts at the intermediate points: the frame pointer, the saved        *)
(* registers and the return address at fixed offsets from stackpointer, RSP  *)
(* and the addresses of the context and the buffer at fixed offsets from     *)
(* bot, the polynomial, the direction flag, which must stay clear for        *)
(* mldsa_shake128_release and the REP STOSQ at the end, and the count, the   *)
(* coefficients so far and the context. The state in the context is kept as  *)
(* 200 bytes, as the 1600-bit (wbytes) form does not survive the push of a   *)
(* CALL, and the theorems of the callees are restated in that form at the    *)
(* start.                                                                    *)
(* ------------------------------------------------------------------------- *)

let POLY_UNIFORM_FRAME =
 `read RSP s = word_add bot (word 328) /\
  read RBP s = word_add stackpointer (word 1479) /\
  read (memory :> bytes64 (word_add stackpointer (word 1447))) s = rbx_init /\
  read (memory :> bytes64 (word_add stackpointer (word 1455))) s = r12_init /\
  read (memory :> bytes64 (word_add stackpointer (word 1463))) s = r13_init /\
  read (memory :> bytes64 (word_add stackpointer (word 1471))) s = r14_init /\
  read (memory :> bytes64 (word_add stackpointer (word 1479))) s = rbp_init /\
  read (memory :> bytes64 (word_add stackpointer (word 1487))) s =
  returnaddress /\
  read R12 s = word_add bot (word 552) /\
  read R13 s = word_add bot (word 344) /\
  read R14 s = a /\
  ~read DF s`;;

let POLY_UNIFORM_POLY =
 `read (R:(x86state,int64)component) s =
  word(MIN 256 (LENGTH(mld_rej_uniform_list (mld_shake128_stream 34 M)
                                            (280 + 56 * i)))) /\
  (!k. k < MIN 256 (LENGTH(mld_rej_uniform_list (mld_shake128_stream 34 M)
                                                (280 + 56 * i)))
       ==> read (memory :> bytes32(word_add a (word(4 * k)))) s =
           EL k (mld_rej_uniform_list (mld_shake128_stream 34 M)
                                      (280 + 56 * i))) /\
  read (memory :> bytes(word_add bot (word 344),200)) s =
  val(keccak_squeeze (5 + i) (S:1600 word)) /\
  read (memory :> bytes32(word_add bot (word 544))) s = word 168`;;

let POLY_UNIFORM_A1 =
  let t = vsubst [`0`,`i:num`; `RAX`,`R:(x86state,int64)component`]
           POLY_UNIFORM_POLY in
  let t' = rhs(concl(REWRITE_CONV[MULT_CLAUSES; ADD_CLAUSES] t)) in
  mk_abs(`s:x86state`,
         list_mk_conj(conjuncts t' @ conjuncts POLY_UNIFORM_FRAME));;

let POLY_UNIFORM_INV =
  list_mk_abs([`i:num`; `s:x86state`],
    list_mk_conj(conjuncts(vsubst [`RBX`,`R:(x86state,int64)component`]
                                  POLY_UNIFORM_POLY) @
                 conjuncts POLY_UNIFORM_FRAME));;

let POLY_UNIFORM_A2 =
  mk_abs(`s:x86state`,
    list_mk_conj(
     `!k. k < 256
          ==> read (memory :> bytes32(word_add a (word(4 * k)))) s =
              EL k (mld_rej_uniform_list (mld_shake128_stream 34 M)
                                         (280 + 56 * k0))` ::
     conjuncts POLY_UNIFORM_FRAME));;

(*** The result from the first 280 + 56 * k0 groups ***)

let POLY_UNIFORM_RESULT = prove
 (`!a:int64 M k0 (s:x86state).
     mld_rej_uniform_terminates (mld_shake128_stream 34 M) /\
     256 <= LENGTH(mld_rej_uniform_list (mld_shake128_stream 34 M)
                                        (280 + 56 * k0)) /\
     (!k. k < 256
          ==> read (memory :> bytes32(word_add a (word(4 * k)))) s =
              EL k (mld_rej_uniform_list (mld_shake128_stream 34 M)
                                         (280 + 56 * k0)))
     ==> (!k. k < 256
              ==> read (memory :> bytes32(word_add a (word(4 * k)))) s =
                  mld_poly_uniform M k)`,
  SIMP_TAC[mld_poly_uniform; MLD_REJ_UNIFORM_POLY_EQ]);;

let POLY_UNIFORM_ABSORB_POS = prove
 (`!r (S:1600 word) pos inlen M.
        SND(mld_keccak_absorb r S pos inlen M) = (pos + inlen) MOD r`,
  REWRITE_TAC[mld_keccak_absorb] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The setup: the callee theorems, with the Keccak states as 200 bytes, the  *)
(* template, the realigned stack frame (k = 1447, as 40 bytes are pushed     *)
(* before the AND, so that the aligned frame and the stacks of the callees   *)
(* are the region (bot,1416)) and the saved registers, the absorbed state S  *)
(* with the stream as its bytes, and k0 with its minimality.                 *)
(* ------------------------------------------------------------------------- *)

let POLY_UNIFORM_INTRO_TAC =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE128_INIT_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_INIT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE128_ABSORB_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_ABSORB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE128_FINALIZE_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_FINALIZE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE128_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_SQUEEZE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE128_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_RELEASE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_REJ_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_REJ" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  CONCRETIZE_F_EVENTS_TAC POLY_UNIFORM_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst POLY_UNIFORM_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

let POLY_UNIFORM_SETUP_TAC =
  REALIGN_TAC 1447 THEN REALIGN_FRAME_TAC 1487 1447 THEN
  REALIGN_NONOV_TAC 1416
   [`a:int64,1024`; `seed:int64,34`; `word pc:int64,51232`;
    `word_add stackpointer (word 1447):int64,40`;
    `word_add stackpointer (word 1487):int64,8`] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ABBREV_TAC `S = mld_keccak_absorb_once 168 0x1F 34 M` THEN
  ASSUME_TAC(SYM(REWRITE_RULE[ASSUME
   `mld_keccak_absorb_once 168 0x1F 34 M = S`]
    (SPECL [`34`; `M:num`] mld_shake128_stream))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MLD_REJ_UNIFORM_TERMINATES) THEN
  ABBREV_TAC `k0 = mld_poly_uniform_nblocks (mld_shake128_stream 34 M)`;;

(*** The seed bound, at the start of the simulation ***)

let POLY_UNIFORM_SEED_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes(seed,34)) s = M`) (concl th)
    then MP_TAC(ISPECL [`seed:int64`; `34`; `read memory (s0:x86state)`]
                       READ_BYTES_BOUND) THEN
         REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; ASSUME(concl th)]
    else NO_TAC) THEN
  DISCH_TAC;;

(*** The states after the absorbing and finalizing ***)

let POLY_UNIFORM_FINALIZED_TAC =
  W(fun (asl,w) ->
    let bth = snd(find (fun (_,th) ->
                can (term_match [] `M < 2 EXP (8 * 34)`) (concl th)) asl) in
    let lth = REWRITE_RULE[POLY_UNIFORM_ABSORB_POS; ADD_CLAUSES]
               (MP (SPECL [`168`; `0x1F`; `34`; `M:num`]
                     MLD_KECCAK_ABSORB_ONCE_SHORT)
                   (CONJ (ARITH_RULE `34 + 2 <= 168`)
                     (CONJ (ARITH_RULE `0x1F < 128`) bth))) in
    let lth' = CONV_RULE(ONCE_DEPTH_CONV NUM_MOD_CONV) lth in
    RULE_ASSUM_TAC(REWRITE_RULE[lth'; ASSUME
      `mld_keccak_absorb_once 168 0x1F 34 M = S`]));;

(*** The blocks after squeezing, as bytes of the stream, and the context, ***)
(*** with the addresses of the bytes in the form of the precondition of   ***)
(*** mld_rej_uniform_c                                                     ***)

let POLY_UNIFORM_SHIFT168 =
  REWRITE_RULE[ARITH_RULE `0 < 168`]
   (SPEC `168` MLD_KECCAK_SQUEEZE_BYTE_SHIFT);;

let POLY_UNIFORM_BLOCKS_TAC =
  let sth = REWRITE_RULE[ARITH_RULE `168 * 5 = 840`; ARITH_RULE `168 * 1 = 168`]
              (CONJ (SPECL [`168`; `S:1600 word`; `5`]
                      MLD_KECCAK_SQUEEZE_STATE_BLOCKS)
                    (SPECL [`168`; `keccak_squeeze (5 + i) (S:1600 word)`;
                            `1`] MLD_KECCAK_SQUEEZE_STATE_BLOCKS)) in
  let sth' = REWRITE_RULE[ARITH_RULE `0 < 168 /\ 0 < 5 /\ 0 < 1`;
                          ARITH_RULE `0 < 168`; ARITH_RULE `0 < 5`;
                          ARITH_RULE `0 < 1`] sth in
  RULE_ASSUM_TAC(REWRITE_RULE[sth'; FST; SND; MLD_KECCAK_SQUEEZE_ADD;
                              ARITH_RULE `1 + 5 + i = 5 + i + 1`]) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes(a,n)) s =
                           num_of_bytelist(list_of_seq f n)`) (concl th)
    then ASSUME_TAC(MATCH_MP MLD_READ_BYTES_LIST_OF_SEQ th)
    else NO_TAC)) THEN
  W(fun (asl,w) ->
    let sts = filter (fun th -> can (term_match []
                `mld_keccak_squeeze_byte 168 S 168 = mld_shake128_stream n m`)
                (concl th)) (map snd asl) in
    RULE_ASSUM_TAC(fun th ->
      if can (term_match [] `!j. j < n ==> read (memory :> bytes8 a) s = y`)
             (concl th)
      then REWRITE_RULE(POLY_UNIFORM_SHIFT168::
                        ARITH_RULE `168 * (5 + i) = 3 * (280 + 56 * i)`::
                        sts) th
      else th)) THEN
  SAMPLING_BYTES_NORMALIZE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The first sampling, from the bytes of the first five blocks. Each CALL is *)
(* a step of its own, before the step of the callee, and RSP gets the value  *)
(* of the AND after step 9.                                                  *)
(* ------------------------------------------------------------------------- *)

let POLY_UNIFORM_PART1_TAC =
  FULL_INIT_TAC THEN POLY_UNIFORM_SEED_TAC THEN
  X86_STEPS_TAC POLY_UNIFORM_EXEC (1--9) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC POLY_UNIFORM_EXEC (10--14) THEN
  POLY_UNIFORM_CALL_TAC "H_INIT" [`read RDI s`] 15 THEN
  X86_STEPS_TAC POLY_UNIFORM_EXEC (16--19) THEN
  POLY_UNIFORM_CALL_TAC "H_ABSORB"
   [`read RDI s`; `read RSI s`; `34`; `word 0:1600 word`; `0`; `M:num`] 20 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[POLY_UNIFORM_ABSORB_POS; ADD_CLAUSES]) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MOD_CONV)) THEN
  X86_STEPS_TAC POLY_UNIFORM_EXEC (21--22) THEN
  POLY_UNIFORM_CALL_TAC "H_FINALIZE"
   [`read RDI s`; `FST(mld_keccak_absorb 168 (word 0) 0 34 M)`; `34`] 23 THEN
  POLY_UNIFORM_FINALIZED_TAC THEN
  X86_STEPS_TAC POLY_UNIFORM_EXEC (24--27) THEN
  POLY_UNIFORM_CALL_TAC "H_SQUEEZE"
   [`read RDI s`; `840`; `read RDX s`; `S:1600 word`; `168`] 28 THEN
  POLY_UNIFORM_BLOCKS_TAC THEN
  X86_STEPS_TAC POLY_UNIFORM_EXEC (29--33) THEN
  POLY_UNIFORM_CALL_TAC "H_REJ"
   [`read RDI s`; `0`; `read RDX s`; `840`; `mld_shake128_stream 34 M`] 34 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_REJ_UNIFORM_CTR_FIRST; LE_0; SUB_0;
                              ARITH_RULE `840 DIV 3 = 280`]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  POLY_UNIFORM_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The tests of the count against 255, by JA and JBE after a 32-bit compare, *)
(* and whether the polynomial is complete after block i + 1.                 *)
(* ------------------------------------------------------------------------- *)

let POLY_UNIFORM_CMP = prove
 (`!c. c < 2 EXP 32
       ==> val(word_zx(word c:int64):int32) = c /\
           (&c - &255:int =
            &(val(word_sub (word_zx (word c:int64):int32) (word 255))) <=>
            255 <= c) /\
           (val(word_sub (word_zx (word c:int64):int32) (word 255)) = 0 <=>
            c = 255)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(word_zx(word c:int64):int32) = c` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
    POP_ASSUM MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[MOD_LT; ARITH_RULE
     `c < 4294967296 ==> c < 18446744073709551616`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN COND_CASES_TAC THENL
   [ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN ASM_ARITH_TAC;
    CONJ_TAC THENL
     [MATCH_MP_TAC(TAUT `~a /\ ~b ==> (a <=> b)`) THEN
      CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
      MATCH_MP_TAC(INT_ARITH
       `x < &255 /\ &0 <= y ==> ~(x - &255:int = y)`) THEN
      REWRITE_TAC[INT_POS; INT_OF_NUM_LT] THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC]]);;

let POLY_UNIFORM_TEST_PROVE_TAC =
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `n0 < 2 EXP 32` ASSUME_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[POLY_UNIFORM_CMP] THEN ASM_ARITH_TAC;;

let POLY_UNIFORM_TEST_TAC c =
  let v = `n0:num` in
  let bth = SPECL [`256`; rand c] (ARITH_RULE `!a b. MIN a b <= a`) in
  FIRST_X_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("RIP",_)),_)),
           Comb(Comb(Comb(Const("COND",_),cnd),_),_)) when free_in c cnd ->
        let mk res = mk_forall(v,mk_imp(`n0 <= 256`,
                                        mk_eq(subst [v,c] cnd,res))) in
        let lth = try prove(mk `255 < n0`,POLY_UNIFORM_TEST_PROVE_TAC)
                  with Failure _ ->
                    prove(mk `~(255 < n0)`,POLY_UNIFORM_TEST_PROVE_TAC) in
        ASSUME_TAC(REWRITE_RULE[MP (SPEC c lth) bth;
                                ARITH_RULE `255 < MIN 256 x <=> 256 <= x`] th)
    | _ -> NO_TAC);;

let POLY_UNIFORM_LS_TAC =
  SUBGOAL_THEN (mk_eq(POLY_UNIFORM_DONE `i + 1`,`~(i + 1 < k0)`))
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [EQ_TAC THENL
     [DISCH_TAC THEN REWRITE_TAC[NOT_LT] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      DISCH_TAC THEN SUBGOAL_THEN `i + 1 = k0` SUBST1_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`i < k0`; `~(i + 1 < k0)`] THEN ARITH_TAC;
        FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The branch round the loop when no more blocks are needed, and the entry   *)
(* to the loop otherwise.                                                    *)
(* ------------------------------------------------------------------------- *)

let POLY_UNIFORM_NOLOOP_TAC =
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES; ADD_CLAUSES]) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN (mk_eq(poly_uniform_count0,`256`))
   (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[ARITH_RULE `MIN a b = a <=> a <= b`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FULL_INIT_TAC THEN
  X86_STEPS_TAC POLY_UNIFORM_EXEC (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
  POLY_UNIFORM_DISCHARGE_TAC;;

let POLY_UNIFORM_LOOP_INIT_TAC =
  FULL_INIT_TAC THEN
  X86_STEPS_TAC POLY_UNIFORM_EXEC (1--2) THEN
  POLY_UNIFORM_TEST_TAC poly_uniform_count0 THEN
  SUBGOAL_THEN (mk_neg(rhs(concl(REWRITE_CONV[MULT_CLAUSES; ADD_CLAUSES]
                                  (POLY_UNIFORM_DONE `0`)))))
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(k0 = 0)` THEN REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM LE_ANTISYM; LE_0] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES];
    ALL_TAC] THEN
  X86_STEPS_TAC POLY_UNIFORM_EXEC (3--4) THEN
  ARGS_32_TAC [poly_uniform_count0] THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
  POLY_UNIFORM_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The loop body, for iteration i, with the count before it as c, its        *)
(* definition put back before the events are matched.                        *)
(* ------------------------------------------------------------------------- *)

let POLY_UNIFORM_ABBREV_TAC =
  let t = poly_uniform_count `i:num` in
  ASSUME_TAC(SPECL [`256`; rand t] (ARITH_RULE `!a b. MIN a b <= a`)) THEN
  ABBREV_TAC(mk_eq(`c:num`,t));;

let POLY_UNIFORM_ABBREV (asl,w) =
  let eq = mk_eq(poly_uniform_count `i:num`,`c:num`) in
  snd(find (fun (_,th) -> concl th = eq) asl);;

let POLY_UNIFORM_UNABBREV_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    concl th = mk_eq(poly_uniform_count `i:num`,`c:num`)));;

let POLY_UNIFORM_COMBINE_TAC n =
  let s = mk_var("s"^string_of_int n,`:x86state`) in
  let strm = `mld_shake128_stream 34 M` in
  let goal = vsubst [s,`s:x86state`]
   `!k. k < MIN 256 (LENGTH(mld_rej_uniform_list (mld_shake128_stream 34 M)
                                                 (280 + 56 * (i + 1))))
        ==> read (memory :> bytes32(word_add a (word(4 * k)))) s =
            EL k (mld_rej_uniform_list (mld_shake128_stream 34 M)
                                       (280 + 56 * (i + 1)))` in
  let isvecfact pat th =
    is_forall(concl th) && free_in `a:int64` (concl th) &&
    free_in s (concl th) && can (term_match [] pat) (concl th) in
  W(fun gl ->
    let ath = POLY_UNIFORM_ABBREV gl in
    let cth = REWRITE_RULE[ARITH_RULE
                `(280 + 56 * i) + 56 = 280 + 56 * (i + 1)`]
               (MATCH_MP MLD_REJ_UNIFORM_CTR_BLOCK ath) in
    RULE_ASSUM_TAC(REWRITE_RULE[cth; ARITH_RULE `168 DIV 3 = 56`]) THEN
    SUBGOAL_THEN goal ASSUME_TAC THENL
     [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      MP_TAC(SPECL [strm; `280 + 56 * i`; `c:num`; `k:num`]
                   MLD_REJ_UNIFORM_EL_BLOCK) THEN
      REWRITE_TAC[ARITH_RULE `(280 + 56 * i) + 56 = 280 + 56 * (i + 1)`] THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[ath]; DISCH_THEN SUBST1_TAC] THEN
      COND_CASES_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check
          (isvecfact `!k. k < c ==> P k`)) THEN
        ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o check
          (isvecfact `!k. c <= k /\ k < d ==> P k`)) THEN
        ASM_REWRITE_TAC[GSYM NOT_LT]];
      ALL_TAC]);;

let POLY_UNIFORM_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  POLY_UNIFORM_ABBREV_TAC THEN
  FULL_INIT_TAC THEN

  (*** Squeezing one more block ***)

  X86_STEPS_TAC POLY_UNIFORM_EXEC (1--4) THEN
  POLY_UNIFORM_CALL_TAC "H_SQUEEZE"
   [`read RDI s`; `168`; `read RDX s`; `keccak_squeeze (5 + i) (S:1600 word)`;
    `168`] 5 THEN
  POLY_UNIFORM_BLOCKS_TAC THEN

  (*** Sampling from the block after the coefficients so far ***)

  X86_STEPS_TAC POLY_UNIFORM_EXEC (6--10) THEN
  ARGS_32_TAC [`c:num`] THEN
  POLY_UNIFORM_CALL_TAC "H_REJ"
   [`read RDI s`; `c:num`; `read RDX s`; `168`;
    `\j. mld_shake128_stream 34 M (3 * (280 + 56 * i) + j)`] 11 THEN
  POLY_UNIFORM_COMBINE_TAC 11 THEN

  (*** The test of whether the polynomial is complete now ***)

  X86_STEPS_TAC POLY_UNIFORM_EXEC (12--14) THEN
  POLY_UNIFORM_TEST_TAC (poly_uniform_count `i + 1`) THEN
  POLY_UNIFORM_LS_TAC THEN
  ARGS_32_TAC [poly_uniform_count `i + 1`] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  POLY_UNIFORM_UNABBREV_TAC THEN POLY_UNIFORM_DISCHARGE_TAC;;

(*** The exit of the loop, where the polynomial has 256 coefficients ***)

let POLY_UNIFORM_EXIT_TAC =
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  SUBGOAL_THEN (mk_eq(poly_uniform_count `k0:num`,`256`))
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  POLY_UNIFORM_DISCHARGE_TAC;;

let POLY_UNIFORM_LOOP_TAC =
  REWRITE_TAC[EQF_INTRO(ASSUME `~(k0 = 0)`)] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `k0:num` `pc + mldsa_poly_uniform_loop1`
   `pc + mldsa_poly_uniform_loop1_exit` POLY_UNIFORM_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    POLY_UNIFORM_LOOP_INIT_TAC;
    POLY_UNIFORM_BODY_TAC;
    POLY_UNIFORM_EXIT_TAC];;

(* ------------------------------------------------------------------------- *)
(* Releasing the context, zeroing the buffer (a REP STOSQ of 105 quadwords), *)
(* and the return, with the polynomial as mld_poly_uniform of the seed.      *)
(* ------------------------------------------------------------------------- *)

let POLY_UNIFORM_PART3_TAC =
  FULL_INIT_TAC THEN
  SUBGOAL_THEN
   `!k. k < 256
        ==> read (memory :> bytes32(word_add a (word(4 * k)))) s0 =
            mld_poly_uniform M k`
  ASSUME_TAC THENL
   [MATCH_MP_TAC POLY_UNIFORM_RESULT THEN EXISTS_TAC `k0:num` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `k0:num`)) THEN
  X86_STEPS_TAC POLY_UNIFORM_EXEC (1--2) THEN
  POLY_UNIFORM_CALL_TAC "H_RELEASE" [`read RDI s`] 3 THEN
  X86_STEPS_TAC POLY_UNIFORM_EXEC (4--14) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  POLY_UNIFORM_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together.                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  POLY_UNIFORM_INTRO_TAC THEN POLY_UNIFORM_SETUP_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa_poly_uniform_loop1_exit`
   POLY_UNIFORM_A2 THEN CONJ_TAC THENL
   [ENSURES_EVENTS_SEQUENCE_TAC
     `pc + mldsa_poly_uniform_after_mld_rej_uniform_c_1`
     POLY_UNIFORM_A1 THEN CONJ_TAC THENL
     [POLY_UNIFORM_PART1_TAC;
      ASM_CASES_TAC `k0 = 0` THENL
       [POLY_UNIFORM_NOLOOP_TAC; POLY_UNIFORM_LOOP_TAC]];
    POLY_UNIFORM_PART3_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
