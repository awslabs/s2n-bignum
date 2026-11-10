(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform sampling of four polynomials mod q from four seeds: the proof     *)
(* (see poly_uniform_4x_spec.ml). As on AArch64, it follows the proof for    *)
(* mlkem_poly_rej_uniform_x4 of mlkem-native, with the FULL theorems of the  *)
(* callees, whose results and events the proof combines at each call. The    *)
(* x86 code aligns its frame to 32 bytes with AND RSP,-32 after saving six   *)
(* registers, so that the state, the buffers and the saved arguments are at  *)
(* fixed offsets from bot, the bottom of the aligned part of the frame (see  *)
(* utils/mldsa_native_realign.ml). Its loop is entered at its test, which    *)
(* compares the four counts with 255 by CMP and SETBE, ORs the bytes for the *)
(* first three and branches back on the result with JNE, and then compares   *)
(* the fourth count, branching back with JBE: an iteration thus takes one of *)
(* two paths, and so does the test before the loop.                          *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/poly_uniform_4x_spec.ml";;
needs "x86/proofs/utils/mldsa_native_sampling.ml";;
needs "x86/proofs/utils/mldsa_native_realign.ml";;

let POLY_UNIFORM_4X_EXEC = MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The seeds, polynomials and absorbed states, and the terms for the number  *)
(* of coefficients of each after t blocks after the first five: the count    *)
(* MIN 256 (LENGTH(mld_rej_uniform_list s (280 + 56 * t))) for the stream s  *)
(* of the seed, and whether polynomials are complete after t blocks.         *)
(* ------------------------------------------------------------------------- *)

let POLY_UNIFORM_4X_MS = [`M0:num`; `M1:num`; `M2:num`; `M3:num`]
and POLY_UNIFORM_4X_VECS =
  [`vec0:int64`; `vec1:int64`; `vec2:int64`; `vec3:int64`]
and POLY_UNIFORM_4X_SVS =
  [`S0:1600 word`; `S1:1600 word`; `S2:1600 word`; `S3:1600 word`];;

let poly_uniform_4x_stream m =
  mk_comb(`mld_shake128_stream 34`,m);;

let poly_uniform_4x_list m t =
  list_mk_comb(`mld_rej_uniform_list`,[poly_uniform_4x_stream m; t]);;

let poly_uniform_4x_groups t =
  mk_binop `(+):num->num->num` `280`
   (mk_binop `( * ):num->num->num` `56` t);;

let poly_uniform_4x_count m t =
  mk_comb(`MIN 256`,mk_comb(`LENGTH:(int32)list->num`,
    poly_uniform_4x_list m (poly_uniform_4x_groups t)));;

let POLY_UNIFORM_4X_ZERO_CONV = REWRITE_CONV[MULT_CLAUSES; ADD_CLAUSES];;

let poly_uniform_4x_count0 m =
  rhs(concl(POLY_UNIFORM_4X_ZERO_CONV (poly_uniform_4x_count m `0`)));;

let poly_uniform_4x_cs0 = map poly_uniform_4x_count0 POLY_UNIFORM_4X_MS
and poly_uniform_4x_cs1 =
  map (fun m -> poly_uniform_4x_count m `i + 1`) POLY_UNIFORM_4X_MS;;

let POLY_UNIFORM_4X_DONE1 m n =
  mk_binop `(<=):num->num->bool` `256`
   (mk_comb(`LENGTH:(int32)list->num`,
            poly_uniform_4x_list m (poly_uniform_4x_groups n)));;

let POLY_UNIFORM_4X_DONE n =
  list_mk_conj(map (fun m -> POLY_UNIFORM_4X_DONE1 m n) POLY_UNIFORM_4X_MS);;

let POLY_UNIFORM_4X_DONE3 n =
  list_mk_conj(map (fun m -> POLY_UNIFORM_4X_DONE1 m n)
                   (butlast POLY_UNIFORM_4X_MS));;

let POLY_UNIFORM_4X_DONE3_0 =
  rhs(concl(POLY_UNIFORM_4X_ZERO_CONV (POLY_UNIFORM_4X_DONE3 `0`)));;

(* ------------------------------------------------------------------------- *)
(* The events, as for mlkem_poly_rej_uniform_x4: those to the end of the     *)
(* four first samplings (p1), of the loop over the k0 more blocks that are   *)
(* needed, k0 being the least number with which all four have 256            *)
(* coefficients, or of the branch round it if k0 = 0, and those of releasing *)
(* the state, zeroing the buffers and returning (p3). The test before the    *)
(* loop and each iteration take one of two paths (entera, enterb, loopa and  *)
(* loopb), the second when the first three polynomials are complete, which   *)
(* tests the fourth with one more compare and branch. The events before a    *)
(* call may depend on bot, which REALIGN_UNBOT_TAC removes before they are   *)
(* matched with the template at the end of each part                         *)
(* (POLY_UNIFORM_4X_DISCHARGE_TAC).                                          *)
(* ------------------------------------------------------------------------- *)

let POLY_UNIFORM_4X_TEMPLATE =
  let args = [`vec0:int64`; `vec1:int64`; `vec2:int64`; `vec3:int64`;
              `seed:int64`; `M0:num`; `M1:num`; `M2:num`; `M3:num`;
              `pc:num`; `stackpointer:int64`; `returnaddress:int64`] in
  let fty = itlist (fun a t -> mk_fun_ty (type_of a) t) args
                   `:(uarch_event)list` in
  let fv n = mk_var(n,fty) in
  let app n = list_mk_comb(fv n,args) in
  let k0 = mk_comb(`(minimal):(num->bool)->num`,
                   mk_abs(`n:num`,POLY_UNIFORM_4X_DONE `n:num`)) in
  let fl n = list_mk_comb(mk_var(n,
               itlist (fun a t -> mk_fun_ty (type_of a) t) args
                      (mk_fun_ty `:num` `:(uarch_event)list`)),args) in
  let loop = mk_abs(`i:num`,mk_cond(POLY_UNIFORM_4X_DONE3 `i + 1`,
                                    mk_comb(fl "f_ev_loopb",`i:num`),
                                    mk_comb(fl "f_ev_loopa",`i:num`))) in
  let enter = mk_cond(POLY_UNIFORM_4X_DONE3_0,app "f_ev_enterb",
                      app "f_ev_entera") in
  let ap = `APPEND:(uarch_event)list->(uarch_event)list->(uarch_event)list` in
  let enum = list_mk_comb(`ENUMERATEL:num->(num->(uarch_event)list)->
                                     (uarch_event)list`,[k0;loop]) in
  let mid = mk_cond(mk_eq(k0,`0`),app "f_ev_skip",
              list_mk_comb(ap,[app "f_ev_exit";
                list_mk_comb(ap,[enum; enter])])) in
  let body = list_mk_comb(ap,[app "f_ev_p3";
               list_mk_comb(ap,[mid; app "f_ev_p1"])]) in
  list_mk_abs(args,body);;

let POLY_UNIFORM_4X_ALLOWED =
  [`pc:num`; `vec0:int64`; `vec1:int64`; `vec2:int64`; `vec3:int64`;
   `seed:int64`; `M0:num`; `M1:num`; `M2:num`; `M3:num`;
   `stackpointer:int64`; `returnaddress:int64`; `bot:int64`; `i:num`;
   `c0:num`; `c1:num`; `c2:num`; `c3:num`];;

let POLY_UNIFORM_4X_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc POLY_UNIFORM_4X_EXEC name
    (ilist @ [`pc:num`; `read RSP s`;
              `read (memory :> bytes64 (read RSP s)) s`])
    POLY_UNIFORM_4X_ALLOWED n;;

let POLY_UNIFORM_4X_DISCHARGE_TAC =
  REALIGN_UNBOT_TAC THEN SAMPLING_PATH_DISCHARGE_SPINE_TAC;;

(*** The instruction after the loop, which has no label in layout.ml ***)

let POLY_UNIFORM_4X_EXIT =
  mk_binop `(+):num->num->num` `pc:num`
   (mk_small_numeral(layout "mldsa_poly_uniform_4x" + 0x1db));;

(* ------------------------------------------------------------------------- *)
(* The facts at the intermediate points: the frame pointer, the saved        *)
(* registers and the return address at fixed offsets from stackpointer, RSP, *)
(* the saved arguments and the addresses of the state and the buffers at     *)
(* fixed offsets from bot, the direction flag, which must stay clear for     *)
(* mldsa_shake128x4_absorb_once, mldsa_shake128x4_release and the REP STOSQ  *)
(* at the end, and for each polynomial its count, the coefficients so far    *)
(* and its state, as 200 bytes, as the 1600-bit (wbytes) form does not       *)
(* survive the push of a CALL. The theorems of the callees are restated in   *)
(* that form at the start. At the exit of the loop the polynomials are       *)
(* complete.                                                                 *)
(* ------------------------------------------------------------------------- *)

let POLY_UNIFORM_4X_ST m =
  mk_comb(mk_comb(`word_add:int64->int64->int64`,`bot:int64`),
          mk_comb(`word:num->int64`,mk_small_numeral(488 + 200 * m)));;

let POLY_UNIFORM_4X_FRAME =
 `read RSP s = word_add bot (word 424) /\
  read RBP s = word_add stackpointer (word 4815) /\
  read (memory :> bytes64 (word_add stackpointer (word 4775))) s = rbx_init /\
  read (memory :> bytes64 (word_add stackpointer (word 4783))) s = r12_init /\
  read (memory :> bytes64 (word_add stackpointer (word 4791))) s = r13_init /\
  read (memory :> bytes64 (word_add stackpointer (word 4799))) s = r14_init /\
  read (memory :> bytes64 (word_add stackpointer (word 4807))) s = r15_init /\
  read (memory :> bytes64 (word_add stackpointer (word 4815))) s = rbp_init /\
  read (memory :> bytes64 (word_add stackpointer (word 4823))) s =
  returnaddress /\
  read (memory :> bytes64 (word_add bot (word 424))) s = vec0 /\
  read (memory :> bytes64 (word_add bot (word 432))) s =
  word_add bot (word 488) /\
  read (memory :> bytes64 (word_add bot (word 440))) s = vec3 /\
  read (memory :> bytes64 (word_add bot (word 448))) s = vec2 /\
  read (memory :> bytes64 (word_add bot (word 456))) s = vec1 /\
  read (memory :> bytes64 (word_add bot (word 472))) s =
  word_add bot (word 3016) /\
  read (memory :> bytes64 (word_add bot (word 480))) s =
  word_add bot (word 2152) /\
  read R14 s = word_add bot (word 1288) /\
  read R15 s = word_add bot (word 3880) /\
  ~read DF s`;;

let POLY_UNIFORM_4X_POLY =
 `read (R:(x86state,int64)component) s =
  word(MIN 256 (LENGTH(mld_rej_uniform_list (mld_shake128_stream 34 M)
                                            (280 + 56 * i)))) /\
  (!k. k < MIN 256 (LENGTH(mld_rej_uniform_list (mld_shake128_stream 34 M)
                                                (280 + 56 * i)))
       ==> read (memory :> bytes32(word_add vec (word(4 * k)))) s =
           EL k (mld_rej_uniform_list (mld_shake128_stream 34 M)
                                      (280 + 56 * i))) /\
  read (memory :> bytes(st,200)) s =
  val(keccak_squeeze (5 + i) (S:1600 word))`;;

let POLY_UNIFORM_4X_POLYS regs =
  flat
   (map (fun (r,(vec,(m,(st,sv)))) ->
          conjuncts
           (vsubst [r,`R:(x86state,int64)component`; vec,`vec:int64`;
                    m,`M:num`; st,`st:int64`; sv,`S:1600 word`]
                   POLY_UNIFORM_4X_POLY))
        (zip regs (zip POLY_UNIFORM_4X_VECS (zip POLY_UNIFORM_4X_MS
           (zip (map POLY_UNIFORM_4X_ST (0--3)) POLY_UNIFORM_4X_SVS)))));;

let POLY_UNIFORM_4X_A1 =
  let t = vsubst [`0`,`i:num`]
           (list_mk_conj(POLY_UNIFORM_4X_POLYS [`R13`; `R12`; `RBX`; `RAX`])) in
  let t' = rhs(concl(POLY_UNIFORM_4X_ZERO_CONV t)) in
  mk_abs(`s:x86state`,
         list_mk_conj(conjuncts t' @ conjuncts POLY_UNIFORM_4X_FRAME));;

let POLY_UNIFORM_4X_INV =
  list_mk_abs([`i:num`; `s:x86state`],
    list_mk_conj(POLY_UNIFORM_4X_POLYS [`R13`; `R12`; `RBX`; `R10`] @
                 conjuncts POLY_UNIFORM_4X_FRAME));;

let POLY_UNIFORM_4X_A2 =
  let res m vec =
    vsubst [m,`M:num`; vec,`vec:int64`]
     `!k. k < 256
          ==> read (memory :> bytes32(word_add vec (word(4 * k)))) s =
              EL k (mld_rej_uniform_list (mld_shake128_stream 34 M)
                                         (280 + 56 * k0))` in
  mk_abs(`s:x86state`,
    list_mk_conj(map2 res POLY_UNIFORM_4X_MS POLY_UNIFORM_4X_VECS @
                 conjuncts POLY_UNIFORM_4X_FRAME));;

(*** The result for one polynomial from the first 280 + 56 * k0 groups ***)

let POLY_UNIFORM_4X_RESULT = prove
 (`!vec:int64 M k0 (s:x86state).
     mld_rej_uniform_terminates (mld_shake128_stream 34 M) /\
     256 <= LENGTH(mld_rej_uniform_list (mld_shake128_stream 34 M)
                                        (280 + 56 * k0)) /\
     (!k. k < 256
          ==> read (memory :> bytes32(word_add vec (word(4 * k)))) s =
              EL k (mld_rej_uniform_list (mld_shake128_stream 34 M)
                                         (280 + 56 * k0)))
     ==> (!k. k < 256
              ==> read (memory :> bytes32(word_add vec (word(4 * k)))) s =
                  mld_poly_uniform M k)`,
  SIMP_TAC[mld_poly_uniform; MLD_REJ_UNIFORM_POLY_EQ]);;

(* ------------------------------------------------------------------------- *)
(* The setup: the callee theorems, the template, the realigned stack frame   *)
(* (k = 4775, as 48 bytes are pushed before the AND, so that the aligned     *)
(* frame and the stacks of the callees are the region (bot,4744)) and the    *)
(* saved registers, the absorbed states S0, ..., S3, with the streams as     *)
(* their bytes, and k0 with its minimality.                                  *)
(* ------------------------------------------------------------------------- *)

let POLY_UNIFORM_4X_INTRO_TAC =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE128X4_INIT_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_INIT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_ABSORB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_SQUEEZE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE128X4_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_RELEASE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_REJ_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_REJ" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  CONCRETIZE_F_EVENTS_TAC POLY_UNIFORM_4X_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst POLY_UNIFORM_4X_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

let POLY_UNIFORM_4X_SETUP_TAC =
  REALIGN_TAC 4775 THEN REALIGN_FRAME_TAC 4823 4775 THEN
  REALIGN_NONOV_TAC 4744
   [`vec0:int64,1024`; `vec1:int64,1024`; `vec2:int64,1024`;
    `vec3:int64,1024`; `seed:int64,34`; `word_add seed (word 64):int64,34`;
    `word_add seed (word 128):int64,34`; `word_add seed (word 192):int64,34`;
    `word pc:int64,51232`;
    `word_add stackpointer (word 4775):int64,48`;
    `word_add stackpointer (word 4823):int64,8`] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15`;;

let POLY_UNIFORM_4X_STATES_TAC =
  MAP_EVERY (fun (m,sv) ->
    let t = vsubst [m,`M:num`] `mld_keccak_absorb_once 168 0x1F 34 M` in
    ABBREV_TAC(mk_eq(sv,t)) THEN
    ASSUME_TAC(SYM(REWRITE_RULE[ASSUME(mk_eq(t,sv))]
                    (SPECL [`34`; m] mld_shake128_stream))))
   (zip POLY_UNIFORM_4X_MS POLY_UNIFORM_4X_SVS);;

let POLY_UNIFORM_4X_MINIMAL_TAC =
  let p = mk_abs(`n:num`,POLY_UNIFORM_4X_DONE `n:num`) in
  let nb m = mk_comb(`mld_poly_uniform_nblocks`,poly_uniform_4x_stream m) in
  let sumnb = end_itlist (mk_binop `(+):num->num->num`)
                         (map nb POLY_UNIFORM_4X_MS) in
  MP_TAC(BETA_RULE(fst(EQ_IMP_RULE(ISPEC p MINIMAL)))) THEN
  ANTS_TAC THENL
   [EXISTS_TAC sumnb THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC MLD_REJ_UNIFORM_TERMINATES_MONO THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC(mk_eq(`k0:num`,mk_comb(`(minimal):(num->bool)->num`,p))) THEN
  STRIP_TAC;;

let POLY_UNIFORM_4X_MINIMALITY_TAC j =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Const("!",_),Abs(v,Comb(Comb(Const("==>",_),
        Comb(Comb(Const("<",_),v'),Var("k0",_))),_))) when v' = v ->
        MP_TAC(SPEC j th)
    | _ -> NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* The states after absorbing, and the blocks after squeezing as bytes of    *)
(* the streams (their addresses normalized as in the precondition of         *)
(* mld_rej_uniform_c), the states after them as bytes.                       *)
(* ------------------------------------------------------------------------- *)

let POLY_UNIFORM_4X_ABSORBED_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM MLD_KECCAK_ABSORB_ONCE]) THEN
  W(fun (asl,w) ->
    let abs = filter (fun th -> can (term_match []
                `mld_keccak_absorb_once r p n m = (S:1600 word)`) (concl th))
               (map snd asl) in
    RULE_ASSUM_TAC(fun th ->
      if can (term_match []
               `read (memory :> bytes(a,200)) s = val(x:1600 word)`)
             (concl th)
      then REWRITE_RULE abs th else th));;

let POLY_UNIFORM_4X_SHIFT168 =
  REWRITE_RULE[ARITH_RULE `0 < 168`]
   (SPEC `168` MLD_KECCAK_SQUEEZE_BYTE_SHIFT);;

let POLY_UNIFORM_4X_BLOCKS_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes(a,168 * n)) s =
                           nsum {i | i < n} f`) (concl th)
    then ASSUME_TAC(MATCH_MP MLD_SQUEEZE_BLOCKS_BYTES8
                     (CONJ (ARITH_RULE `0 < 168`) th))
    else NO_TAC)) THEN
  W(fun (asl,w) ->
    let sts = filter (fun th -> can (term_match []
                `mld_keccak_squeeze_byte 168 S 168 = mld_shake128_stream n m`)
                (concl th)) (map snd asl) in
    RULE_ASSUM_TAC(fun th ->
      if can (term_match [] `!j. j < 168 * n ==> P j`) (concl th)
      then CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
            (REWRITE_RULE(POLY_UNIFORM_4X_SHIFT168::
                          ARITH_RULE `168 * (5 + i) = 3 * (280 + 56 * i)`::
                          sts) th)
      else th)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_KECCAK_SQUEEZE_ADD;
                              ARITH_RULE `1 + 5 + i = 5 + i + 1`]) THEN
  SAMPLING_BYTES_NORMALIZE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The four first samplings, from the bytes of the first five blocks. Each   *)
(* CALL is a step of its own, before the step of the callee, and RSP gets    *)
(* the value of the AND after step 10.                                       *)
(* ------------------------------------------------------------------------- *)

let POLY_UNIFORM_4X_CALL0_TAC m n =
  POLY_UNIFORM_4X_CALL_TAC "H_REJ"
   [`read RDI s`; `0`; `read RDX s`; `840`;
    poly_uniform_4x_stream (el m POLY_UNIFORM_4X_MS)] n THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_REJ_UNIFORM_CTR_FIRST; LE_0; SUB_0;
                              ARITH_RULE `840 DIV 3 = 280`]);;

let POLY_UNIFORM_4X_PART1_TAC =
  FULL_INIT_TAC THEN
  X86_STEPS_TAC POLY_UNIFORM_4X_EXEC (1--10) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC POLY_UNIFORM_4X_EXEC (11--21) THEN
  POLY_UNIFORM_4X_CALL_TAC "H_INIT" [`read RDI s`] 22 THEN
  X86_STEPS_TAC POLY_UNIFORM_4X_EXEC (23--30) THEN
  POLY_UNIFORM_4X_CALL_TAC "H_ABSORB"
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `read R8 s`;
    `34`; `M0:num`; `M1:num`; `M2:num`; `M3:num`] 31 THEN
  POLY_UNIFORM_4X_ABSORBED_TAC THEN
  X86_STEPS_TAC POLY_UNIFORM_4X_EXEC (32--43) THEN
  POLY_UNIFORM_4X_CALL_TAC "H_SQUEEZE"
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `5`;
    `read R9 s`; `S0:1600 word`; `S1:1600 word`; `S2:1600 word`;
    `S3:1600 word`] 44 THEN
  POLY_UNIFORM_4X_BLOCKS_TAC THEN
  MAP_EVERY (fun (m,(n1,n2)) ->
    X86_STEPS_TAC POLY_UNIFORM_4X_EXEC (n1--(n2-1)) THEN
    POLY_UNIFORM_4X_CALL0_TAC m n2)
   (zip (0--3) [45,50; 51,57; 58,64; 65,71]) THEN
  ARGS_32_TAC (butlast poly_uniform_4x_cs0) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  POLY_UNIFORM_4X_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The test of the loop, as described at the start: SAMPLING_COUNT_TEST_TAC  *)
(* puts the condition of the JNE in the form that the first three            *)
(* polynomials are not complete, and that of the JBE in the form that the    *)
(* fourth is not; the high bits of RDX, which the code ORs into RAX, are     *)
(* unknown, and named rdx0 so that the facts that depend on them are kept.   *)
(* When the first three are complete, whether the fourth is after block i +  *)
(* 1 is whether i + 1 = k0, by the minimality of k0.                         *)
(* ------------------------------------------------------------------------- *)

let POLY_UNIFORM_4X_TEST3_TAC cs =
  SAMPLING_COUNT_TEST_TAC cs `~(255 < n0 /\ 255 < n1 /\ 255 < n2)`;;

let POLY_UNIFORM_4X_TEST1_TAC cs =
  SAMPLING_COUNT_TEST_TAC [last cs] `~(255 < n0)`;;

let POLY_UNIFORM_4X_DONE1_0 m =
  rhs(concl(POLY_UNIFORM_4X_ZERO_CONV (POLY_UNIFORM_4X_DONE1 m `0`)));;

(*** Rewrite the RIP fact only with th ***)

let POLY_UNIFORM_4X_RIP_REWRITE_TAC th =
  FIRST_X_ASSUM(fun rth ->
    if can (term_match [] `read RIP s = (x:int64)`) (concl rth)
    then ASSUME_TAC(REWRITE_RULE[th] rth) else NO_TAC);;

let POLY_UNIFORM_4X_LAST_TAC =
  SUBGOAL_THEN (mk_eq(POLY_UNIFORM_4X_DONE1 `M3:num` `i + 1`,
                      `~(i + 1 < k0)`))
   POLY_UNIFORM_4X_RIP_REWRITE_TAC THENL
   [EQ_TAC THENL
     [DISCH_TAC THEN POLY_UNIFORM_4X_MINIMALITY_TAC `i + 1` THEN
      REWRITE_TAC[ASSUME(POLY_UNIFORM_4X_DONE3 `i + 1`);
                  ASSUME(POLY_UNIFORM_4X_DONE1 `M3:num` `i + 1`)];
      DISCH_TAC THEN SUBGOAL_THEN `i + 1 = k0` SUBST1_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`i < k0`; `~(i + 1 < k0)`] THEN ARITH_TAC;
        FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC];;

let POLY_UNIFORM_4X_NOTLAST_TAC =
  SUBGOAL_THEN `i + 1 < k0` (fun th ->
    POLY_UNIFORM_4X_RIP_REWRITE_TAC(EQT_INTRO th) THEN ASSUME_TAC th) THENL
   [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `k0 = i + 1` SUBST_ALL_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`i < k0`; `k0 <= i + 1`] THEN ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC(mk_neg(POLY_UNIFORM_4X_DONE3 `i + 1`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The branch round the loop when no more blocks are needed, and the entry   *)
(* to the loop otherwise, by either path.                                    *)
(* ------------------------------------------------------------------------- *)

let POLY_UNIFORM_4X_NOLOOP_TAC =
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES; ADD_CLAUSES]) THEN
  REWRITE_TAC[] THEN
  FULL_INIT_TAC THEN ABBREV_TAC `rdx0 = read RDX s0` THEN
  X86_STEPS_TAC POLY_UNIFORM_4X_EXEC (1--11) THEN
  POLY_UNIFORM_4X_TEST3_TAC poly_uniform_4x_cs0 THEN
  SUBGOAL_THEN POLY_UNIFORM_4X_DONE3_0 ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; SAMPLING_CASE_REWRITE_TAC] THEN
  X86_STEPS_TAC POLY_UNIFORM_4X_EXEC (12--13) THEN
  POLY_UNIFORM_4X_TEST1_TAC poly_uniform_4x_cs0 THEN
  SUBGOAL_THEN (POLY_UNIFORM_4X_DONE1_0 `M3:num`)
   POLY_UNIFORM_4X_RIP_REWRITE_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY (fun c ->
    SUBGOAL_THEN (mk_eq(c,`256`))
     (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[ARITH_RULE `MIN a b = a <=> a <= b`] THEN ASM_REWRITE_TAC[];
      ALL_TAC]) poly_uniform_4x_cs0 THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
  POLY_UNIFORM_4X_DISCHARGE_TAC;;

let POLY_UNIFORM_4X_LOOP_INIT_TAC =
  FULL_INIT_TAC THEN ABBREV_TAC `rdx0 = read RDX s0` THEN
  X86_STEPS_TAC POLY_UNIFORM_4X_EXEC (1--11) THEN
  POLY_UNIFORM_4X_TEST3_TAC poly_uniform_4x_cs0 THEN
  ARGS_32_TAC [last poly_uniform_4x_cs0] THEN
  ASM_CASES_TAC POLY_UNIFORM_4X_DONE3_0 THEN SAMPLING_CASE_REWRITE_TAC THENL
   [X86_STEPS_TAC POLY_UNIFORM_4X_EXEC (12--13) THEN
    POLY_UNIFORM_4X_TEST1_TAC poly_uniform_4x_cs0 THEN
    SUBGOAL_THEN (mk_neg(POLY_UNIFORM_4X_DONE1_0 `M3:num`))
     POLY_UNIFORM_4X_RIP_REWRITE_TAC THENL
     [POLY_UNIFORM_4X_MINIMALITY_TAC `0` THEN
      REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
      ANTS_TAC THENL [UNDISCH_TAC `~(k0 = 0)` THEN ARITH_TAC; REWRITE_TAC[]];
      ALL_TAC];
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
  POLY_UNIFORM_4X_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The loop body, for iteration i. The counts before it are c0, ..., c3,     *)
(* their definitions packed into one conjunction, which keeps them from the  *)
(* arithmetic of NONOVERLAPPING_TAC, and put back before the events are      *)
(* matched with the template. After squeezing one more block of each, each   *)
(* call of mld_rej_uniform_c adds the accepted values of its 56 groups after *)
(* the count, giving those of the first 280 + 56 * (i + 1) groups. The count *)
(* of the fourth is kept in the frame across the call of                     *)
(* mldsa_shake128x4_squeezeblocks.                                           *)
(* ------------------------------------------------------------------------- *)

let POLY_UNIFORM_4X_IS_ABBREV tm =
  match tm with
    Comb(Comb(Const("=",_),Comb(Comb(Const("MIN",_),_),_)),Var(n,_)) ->
      String.length n = 2 && String.sub n 0 1 = "c"
  | _ -> false;;

let POLY_UNIFORM_4X_ABBREV_TAC =
  MAP_EVERY (fun m ->
    let t = poly_uniform_4x_count (el m POLY_UNIFORM_4X_MS) `i:num` in
    ASSUME_TAC(SPECL [`256`; rand t] (ARITH_RULE `!a b. MIN a b <= a`)) THEN
    ABBREV_TAC(mk_eq(mk_var("c"^string_of_int m,`:num`),t))) (0--3) THEN
  (fun (asl,w) ->
    let hs,ks = partition (fun (_,th) -> POLY_UNIFORM_4X_IS_ABBREV(concl th))
                          asl in
    let cth = end_itlist CONJ (map snd hs) in
    (null_meta,[("",ASSUME(concl cth))::ks,w],
     fun i ths -> PROVE_HYP (INSTANTIATE_ALL i cth) (hd ths)));;

let POLY_UNIFORM_4X_ABBREV m =
  let eq = mk_eq(poly_uniform_4x_count (el m POLY_UNIFORM_4X_MS) `i:num`,
                 mk_var("c"^string_of_int m,`:num`)) in
  fun (asl,w) ->
    tryfind (fun (_,th) -> find (fun th' -> concl th' = eq) (CONJUNCTS th))
            asl;;

let POLY_UNIFORM_4X_UNABBREV_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_conj(concl th) && POLY_UNIFORM_4X_IS_ABBREV(lhand(concl th))
    then MAP_EVERY (SUBST_ALL_TAC o SYM) (CONJUNCTS th) else NO_TAC);;

let POLY_UNIFORM_4X_COMBINE_TAC m n =
  let mv = el m POLY_UNIFORM_4X_MS and vec = el m POLY_UNIFORM_4X_VECS in
  let c = mk_var("c"^string_of_int m,`:num`)
  and s = mk_var("s"^string_of_int n,`:x86state`) in
  let strm = poly_uniform_4x_stream mv in
  let goal = vsubst [vec,`vec:int64`; strm,`str:num->byte`; s,`s:x86state`]
   `!k. k < MIN 256 (LENGTH(mld_rej_uniform_list str (280 + 56 * (i + 1))))
        ==> read (memory :> bytes32(word_add vec (word(4 * k)))) s =
            EL k (mld_rej_uniform_list str (280 + 56 * (i + 1)))` in
  let isvecfact pat th =
    is_forall(concl th) && free_in vec (concl th) && free_in s (concl th) &&
    can (term_match [] pat) (concl th) in
  W(fun gl ->
    let ath = POLY_UNIFORM_4X_ABBREV m gl in
    let cth = REWRITE_RULE[ARITH_RULE
                `(280 + 56 * i) + 56 = 280 + 56 * (i + 1)`]
               (MATCH_MP MLD_REJ_UNIFORM_CTR_BLOCK ath) in
    RULE_ASSUM_TAC(REWRITE_RULE[cth; ARITH_RULE `168 DIV 3 = 56`]) THEN
    SUBGOAL_THEN goal ASSUME_TAC THENL
     [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      MP_TAC(SPECL [strm; `280 + 56 * i`; c; `k:num`]
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

let POLY_UNIFORM_4X_CALL1_TAC m n =
  let mv = el m POLY_UNIFORM_4X_MS in
  let c = mk_var("c"^string_of_int m,`:num`) in
  let b = mk_abs(`j:num`,
           mk_comb(poly_uniform_4x_stream mv,
                   `3 * (280 + 56 * i) + j`)) in
  ARGS_32_TAC [c] THEN
  POLY_UNIFORM_4X_CALL_TAC "H_REJ"
   [`read RDI s`; c; `read RDX s`; `168`; b] n THEN
  POLY_UNIFORM_4X_COMBINE_TAC m n;;

let POLY_UNIFORM_4X_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  POLY_UNIFORM_4X_ABBREV_TAC THEN
  FULL_INIT_TAC THEN

  (*** Squeezing one more block from each state ***)

  X86_STEPS_TAC POLY_UNIFORM_4X_EXEC (1--8) THEN
  POLY_UNIFORM_4X_CALL_TAC "H_SQUEEZE"
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `1`; `read R9 s`;
    `keccak_squeeze (5 + i) (S0:1600 word)`;
    `keccak_squeeze (5 + i) (S1:1600 word)`;
    `keccak_squeeze (5 + i) (S2:1600 word)`;
    `keccak_squeeze (5 + i) (S3:1600 word)`] 9 THEN
  POLY_UNIFORM_4X_BLOCKS_TAC THEN

  (*** Sampling from each block after the coefficients so far ***)

  MAP_EVERY (fun (m,(n1,n2)) ->
    X86_STEPS_TAC POLY_UNIFORM_4X_EXEC (n1--(n2-1)) THEN
    POLY_UNIFORM_4X_CALL1_TAC m n2)
   (zip (0--3) [10,15; 16,22; 23,29; 30,36]) THEN

  (*** The test of whether all four have 256 coefficients now ***)

  ARGS_32_TAC poly_uniform_4x_cs1 THEN
  ABBREV_TAC `rdx0 = read RDX s36` THEN
  X86_STEPS_TAC POLY_UNIFORM_4X_EXEC (37--46) THEN
  POLY_UNIFORM_4X_TEST3_TAC poly_uniform_4x_cs1 THEN
  ASM_CASES_TAC (POLY_UNIFORM_4X_DONE3 `i + 1`) THEN
  SAMPLING_CASE_REWRITE_TAC THENL
   [X86_STEPS_TAC POLY_UNIFORM_4X_EXEC (47--48) THEN
    POLY_UNIFORM_4X_TEST1_TAC poly_uniform_4x_cs1 THEN
    POLY_UNIFORM_4X_LAST_TAC;
    POLY_UNIFORM_4X_NOTLAST_TAC] THEN
  ARGS_32_TAC poly_uniform_4x_cs1 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(CONJ_TAC THENL
       [COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC; ALL_TAC]) THEN
  POLY_UNIFORM_4X_UNABBREV_TAC THEN POLY_UNIFORM_4X_DISCHARGE_TAC;;

(*** The exit of the loop, where all four have 256 coefficients ***)

let POLY_UNIFORM_4X_EXIT_TAC =
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  MAP_EVERY (fun m ->
    SUBGOAL_THEN (mk_eq(poly_uniform_4x_count m `k0:num`,`256`))
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC]) POLY_UNIFORM_4X_MS THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  POLY_UNIFORM_4X_DISCHARGE_TAC;;

let POLY_UNIFORM_4X_LOOP_TAC =
  REWRITE_TAC[EQF_INTRO(ASSUME `~(k0 = 0)`)] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `k0:num` `pc + mldsa_poly_uniform_4x_join1`
   POLY_UNIFORM_4X_EXIT POLY_UNIFORM_4X_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    POLY_UNIFORM_4X_LOOP_INIT_TAC;
    POLY_UNIFORM_4X_BODY_TAC;
    POLY_UNIFORM_4X_EXIT_TAC];;

(* ------------------------------------------------------------------------- *)
(* Releasing the state, zeroing the buffers (a REP STOSQ of 432 quadwords)   *)
(* and the return, with the polynomials as mld_poly_uniform of the seeds.    *)
(* ------------------------------------------------------------------------- *)

let POLY_UNIFORM_4X_RESULTS_TAC =
  MAP_EVERY (fun (m,vec) ->
    SUBGOAL_THEN
     (vsubst [m,`M:num`; vec,`vec:int64`]
       `!k. k < 256
            ==> read (memory :> bytes32(word_add vec (word(4 * k)))) s0 =
                mld_poly_uniform M k`)
     ASSUME_TAC THENL
     [MATCH_MP_TAC POLY_UNIFORM_4X_RESULT THEN EXISTS_TAC `k0:num` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC])
   (zip POLY_UNIFORM_4X_MS POLY_UNIFORM_4X_VECS);;

let POLY_UNIFORM_4X_PART3_TAC =
  FULL_INIT_TAC THEN POLY_UNIFORM_4X_RESULTS_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `k0:num`)) THEN
  X86_STEPS_TAC POLY_UNIFORM_4X_EXEC (1--2) THEN
  POLY_UNIFORM_4X_CALL_TAC "H_RELEASE" [`read RDI s`] 3 THEN
  X86_STEPS_TAC POLY_UNIFORM_4X_EXEC (4--15) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  POLY_UNIFORM_4X_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together.                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  POLY_UNIFORM_4X_INTRO_TAC THEN POLY_UNIFORM_4X_SETUP_TAC THEN
  POLY_UNIFORM_4X_STATES_TAC THEN POLY_UNIFORM_4X_MINIMAL_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC POLY_UNIFORM_4X_EXIT POLY_UNIFORM_4X_A2 THEN
  CONJ_TAC THENL
   [ENSURES_EVENTS_SEQUENCE_TAC
     `pc + mldsa_poly_uniform_4x_after_mld_rej_uniform_c_4`
     POLY_UNIFORM_4X_A1 THEN CONJ_TAC THENL
     [POLY_UNIFORM_4X_PART1_TAC;
      ASM_CASES_TAC `k0 = 0` THENL
       [POLY_UNIFORM_4X_NOLOOP_TAC; POLY_UNIFORM_4X_LOOP_TAC]];
    POLY_UNIFORM_4X_PART3_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
