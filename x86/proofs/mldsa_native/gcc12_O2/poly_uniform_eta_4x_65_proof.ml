(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling of four polynomials with coefficients in [-4,4] for ML-DSA-65:   *)
(* the proof (see poly_uniform_eta_4x_65_spec.ml). As on AArch64, it follows *)
(* the proof for mldsa_poly_uniform_4x, with the extended seeds of           *)
(* mldsa65_poly_uniform_gamma1_4x, except that the events may depend on the  *)
(* seed only through the lists dc0, ..., dc3 of the values that the calls of *)
(* mld_rej_eta_c65 declassify: the counts of coefficients, on which the loop *)
(* test branches and which the calls get, are numbers of T in initial        *)
(* segments of these lists, and the values that a call declassifies are a    *)
(* sublist. As for the x86 code of mldsa_poly_uniform_4x, the frame is       *)
(* aligned to 32 bytes (see utils/mldsa_native_realign.ml), and the test of  *)
(* the loop takes one of two paths. The code copies the seed with 128-bit    *)
(* SSE loads and stores, the stores aligned (MOVAPS), and loads the nonces   *)
(* that the caller puts on the stack as 32-bit words.                        *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/poly_uniform_eta_4x_65_spec.ml";;
needs "x86/proofs/utils/mldsa_native_sampling.ml";;
needs "x86/proofs/utils/mldsa_native_realign.ml";;

let ETA_4X_65_EXEC = MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The nonces, the inputs and outputs of SHAKE256, the declassified lists    *)
(* dc0 to dc3, the absorbed states, and the count of coefficients of each    *)
(* after t blocks after the first two (272 bytes), as a number of T in D,    *)
(* and whether polynomials are complete after t blocks.                      *)
(* ------------------------------------------------------------------------- *)

let ETA_4X_65_NONCES =
  [`word_zx(n0:int64):byte`; `word_zx(n1:int64):byte`;
   `word_zx(n2:int64):byte`; `word_zx(n3:int64):byte`]
and ETA_4X_65_DS =
  [`dc0:bool list`; `dc1:bool list`; `dc2:bool list`; `dc3:bool list`]
and ETA_4X_65_VECS = [`r0:int64`; `r1:int64`; `r2:int64`; `r3:int64`]
and ETA_4X_65_SVS =
  [`S0:1600 word`; `S1:1600 word`; `S2:1600 word`; `S3:1600 word`];;

let eta_4x_65_input h = vsubst [h,`h:byte`] `sd + 2 EXP 512 * val(h:byte)`;;

let eta_4x_65_stream h =
  mk_comb(`mld_shake256_stream 66`,eta_4x_65_input h);;

let eta_4x_65_declass h =
  mk_comb(`mld_poly_uniform_eta_declass 4`,eta_4x_65_stream h);;

let eta_4x_65_groups t =
  mk_binop `(+):num->num->num` `272`
   (mk_binop `( * ):num->num->num` `136` t);;

let eta_4x_65_count d t =
  vsubst [d,`D:bool list`; eta_4x_65_groups t,`n:num`]
   `MIN 256 (LENGTH(FILTER (\x:bool. x) (SUB_LIST(0,2 * n) D)))`;;

let ETA_4X_65_ZERO_RULES =
  [MULT_CLAUSES; ADD_CLAUSES; ARITH_RULE `2 * 272 = 544`];;

let ETA_4X_65_ZERO_CONV = REWRITE_CONV ETA_4X_65_ZERO_RULES;;

let eta_4x_65_count0 d =
  rhs(concl(ETA_4X_65_ZERO_CONV (eta_4x_65_count d `0`)));;

let eta_4x_65_cs0 = map eta_4x_65_count0 ETA_4X_65_DS
and eta_4x_65_cs1 = map (fun d -> eta_4x_65_count d `i + 1`) ETA_4X_65_DS;;

let ETA_4X_65_DONE1 d n =
  vsubst [d,`D:bool list`; eta_4x_65_groups n,`n:num`]
   `256 <= LENGTH(FILTER (\x:bool. x) (SUB_LIST(0,2 * n) D))`;;

let ETA_4X_65_DONE n =
  list_mk_conj(map (fun d -> ETA_4X_65_DONE1 d n) ETA_4X_65_DS);;

let ETA_4X_65_DONE3 n =
  list_mk_conj(map (fun d -> ETA_4X_65_DONE1 d n) (butlast ETA_4X_65_DS));;

let ETA_4X_65_DONE3_0 =
  rhs(concl(ETA_4X_65_ZERO_CONV (ETA_4X_65_DONE3 `0`)));;

let ETA_4X_65_DONE1_0 d =
  rhs(concl(ETA_4X_65_ZERO_CONV (ETA_4X_65_DONE1 d `0`)));;

(* ------------------------------------------------------------------------- *)
(* The events, as for mldsa_poly_uniform_4x, with the loop over the k0 more  *)
(* blocks that are needed, k0 being now a function of dc0, ..., dc3, and the *)
(* two paths of the test before the loop and of each iteration.              *)
(* ------------------------------------------------------------------------- *)

let ETA_4X_65_TEMPLATE =
  let args = [`r0:int64`; `r1:int64`; `r2:int64`; `r3:int64`;
              `seed:int64`; `dc0:bool list`; `dc1:bool list`; `dc2:bool list`;
              `dc3:bool list`; `pc:num`; `stackpointer:int64`;
              `returnaddress:int64`] in
  let fty = itlist (fun a t -> mk_fun_ty (type_of a) t) args
                   `:(uarch_event)list` in
  let fv n = mk_var(n,fty) in
  let app n = list_mk_comb(fv n,args) in
  let k0 = mk_comb(`(minimal):(num->bool)->num`,
                   mk_abs(`n:num`,ETA_4X_65_DONE `n:num`)) in
  let fl n = list_mk_comb(mk_var(n,
               itlist (fun a t -> mk_fun_ty (type_of a) t) args
                      (mk_fun_ty `:num` `:(uarch_event)list`)),args) in
  let loop = mk_abs(`i:num`,mk_cond(ETA_4X_65_DONE3 `i + 1`,
                                    mk_comb(fl "f_ev_loopb",`i:num`),
                                    mk_comb(fl "f_ev_loopa",`i:num`))) in
  let enter = mk_cond(ETA_4X_65_DONE3_0,app "f_ev_enterb",
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

let ETA_4X_65_ALLOWED =
  [`pc:num`; `r0:int64`; `r1:int64`; `r2:int64`; `r3:int64`;
   `seed:int64`; `dc0:bool list`; `dc1:bool list`; `dc2:bool list`;
   `dc3:bool list`; `stackpointer:int64`; `returnaddress:int64`;
   `bot:int64`; `i:num`; `c0:num`; `c1:num`; `c2:num`; `c3:num`];;

let ETA_4X_65_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc ETA_4X_65_EXEC name
    (ilist @ [`pc:num`; `read RSP s`;
              `read (memory :> bytes64 (read RSP s)) s`])
    ETA_4X_65_ALLOWED n;;

(*** The instruction after the loop, which has no label in layout.ml ***)

let ETA_4X_65_EXIT =
  mk_binop `(+):num->num->num` `pc:num`
   (mk_small_numeral(layout "mldsa65_poly_uniform_eta_4x" + 0x2d4));;

let ETA_4X_65_DISCHARGE_TAC =
  REALIGN_UNBOT_TAC THEN SAMPLING_PATH_DISCHARGE_SPINE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The facts at the intermediate points: the frame pointer, the saved        *)
(* registers and the return address at fixed offsets from stackpointer, RSP, *)
(* the saved arguments and the addresses of the extended seeds, the buffers  *)
(* and the state at fixed offsets from bot, the direction flag, and for each *)
(* polynomial its count, the coefficients so far and its state, as 200       *)
(* bytes; at the exit of the loop the polynomials are complete.              *)
(* ------------------------------------------------------------------------- *)

let ETA_4X_65_EXT m =
  mk_comb(mk_comb(`word_add:int64->int64->int64`,`bot:int64`),
          mk_comb(`word:num->int64`,mk_small_numeral(520 + 96 * m)));;

let ETA_4X_65_ST m =
  mk_comb(mk_comb(`word_add:int64->int64->int64`,`bot:int64`),
          mk_comb(`word:num->int64`,mk_small_numeral(904 + 200 * m)));;

let ETA_4X_65_FRAME =
 `read RSP s = word_add bot (word 424) /\
  read RBP s = word_add stackpointer (word 2927) /\
  read (memory :> bytes64 (word_add stackpointer (word 2887))) s = rbx_init /\
  read (memory :> bytes64 (word_add stackpointer (word 2895))) s = r12_init /\
  read (memory :> bytes64 (word_add stackpointer (word 2903))) s = r13_init /\
  read (memory :> bytes64 (word_add stackpointer (word 2911))) s = r14_init /\
  read (memory :> bytes64 (word_add stackpointer (word 2919))) s = r15_init /\
  read (memory :> bytes64 (word_add stackpointer (word 2927))) s = rbp_init /\
  read (memory :> bytes64 (word_add stackpointer (word 2935))) s =
  returnaddress /\
  read (memory :> bytes64 (word_add bot (word 448))) s =
  word_add bot (word 520) /\
  read (memory :> bytes64 (word_add bot (word 456))) s =
  word_add bot (word 904) /\
  read (memory :> bytes64 (word_add bot (word 464))) s = r3 /\
  read (memory :> bytes64 (word_add bot (word 472))) s = r2 /\
  read (memory :> bytes64 (word_add bot (word 480))) s = r1 /\
  read (memory :> bytes64 (word_add bot (word 488))) s = r0 /\
  read (memory :> bytes64 (word_add bot (word 504))) s =
  word_add bot (word 1992) /\
  read (memory :> bytes64 (word_add bot (word 512))) s =
  word_add bot (word 2568) /\
  read R14 s = word_add bot (word 1704) /\
  read R15 s = word_add bot (word 2280) /\
  ~read DF s`;;

let ETA_4X_65_POLY =
 `read (R:(x86state,int64)component) s =
  word(MIN 256 (LENGTH(FILTER (\x:bool. x)
                        (SUB_LIST(0,2 * (272 + 136 * i)) D)))) /\
  (!k. k < MIN 256 (LENGTH(FILTER (\x:bool. x)
                            (SUB_LIST(0,2 * (272 + 136 * i)) D)))
       ==> read (memory :> bytes32(word_add vec (word(4 * k)))) s =
           EL k (mld_rej_eta_list 4 str (2 * (272 + 136 * i)))) /\
  read (memory :> bytes(st,200)) s =
  val(keccak_squeeze (2 + i) (S:1600 word))`;;

let ETA_4X_65_POLYS regs =
  flat
   (map (fun (r,(vec,(h,(d,(st,sv))))) ->
          conjuncts
           (vsubst [r,`R:(x86state,int64)component`; vec,`vec:int64`;
                    d,`D:bool list`; eta_4x_65_stream h,`str:num->byte`;
                    st,`st:int64`; sv,`S:1600 word`]
                   ETA_4X_65_POLY))
        (zip regs (zip ETA_4X_65_VECS (zip ETA_4X_65_NONCES
           (zip ETA_4X_65_DS (zip (map ETA_4X_65_ST (0--3))
                                  ETA_4X_65_SVS))))));;

let ETA_4X_65_A1 =
  let t = vsubst [`0`,`i:num`]
           (list_mk_conj(ETA_4X_65_POLYS [`R13`; `R12`; `RBX`; `RAX`])) in
  let t' = rhs(concl(ETA_4X_65_ZERO_CONV t)) in
  mk_abs(`s:x86state`,
         list_mk_conj(conjuncts t' @ conjuncts ETA_4X_65_FRAME));;

let ETA_4X_65_INV =
  list_mk_abs([`i:num`; `s:x86state`],
    list_mk_conj(ETA_4X_65_POLYS [`R13`; `R12`; `RBX`; `R10`] @
                 conjuncts ETA_4X_65_FRAME));;

let ETA_4X_65_A2 =
  let res h vec =
    vsubst [eta_4x_65_stream h,`str:num->byte`; vec,`vec:int64`]
     `!k. k < 256
          ==> read (memory :> bytes32(word_add vec (word(4 * k)))) s =
              EL k (mld_rej_eta_list 4 str (2 * (272 + 136 * k0)))` in
  mk_abs(`s:x86state`,
    list_mk_conj(map2 res ETA_4X_65_NONCES ETA_4X_65_VECS @
                 conjuncts ETA_4X_65_FRAME));;

(*** The result for one polynomial from the first 272 + 136 * k0 bytes ***)

let ETA_4X_65_RESULT = prove
 (`!vec:int64 sd (h:byte) D k0 (s:x86state).
     mld_rej_eta_terminates 4 (mld_shake256_stream 66 (sd + 2 EXP 512 * val h))
     /\
     mld_poly_uniform_eta_declass 4
      (mld_shake256_stream 66 (sd + 2 EXP 512 * val h)) = D /\
     256 <= LENGTH(FILTER (\x. x) (SUB_LIST(0,2 * (272 + 136 * k0)) D)) /\
     (!k. k < 256
          ==> read (memory :> bytes32(word_add vec (word(4 * k)))) s =
              EL k (mld_rej_eta_list 4
                     (mld_shake256_stream 66 (sd + 2 EXP 512 * val h))
                     (2 * (272 + 136 * k0))))
     ==> (!k. k < 256
              ==> read (memory :> bytes32(word_add vec (word(4 * k)))) s =
                  mld_poly_uniform_eta 4 sd h k)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `D:bool list`)) THEN
  ASM_SIMP_TAC[mld_poly_uniform_eta] THEN
  MATCH_MP_TAC(REWRITE_RULE[ARITH_EQ; ARITH_RULE
    `2 * 136 * (2 + k) = 2 * (272 + 136 * k)`]
   (SPEC `4` MLD_REJ_ETA_POLY_EQ)) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPEC `2 * (272 + 136 * k0)` o
    MATCH_MP (SPEC `4` MLD_POLY_UNIFORM_ETA_COUNT)) THEN
  UNDISCH_TAC
   `256 <= LENGTH(FILTER (\x. x) (SUB_LIST(0,2 * (272 + 136 * k0))
     (mld_poly_uniform_eta_declass 4
       (mld_shake256_stream 66 (sd + 2 EXP 512 * val(h:byte))))))` THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The setup: the callee theorems, with the Keccak states as 200 bytes, the  *)
(* template, the realigned stack frame (k = 2887, as 48 bytes are pushed     *)
(* before the AND, so that the aligned frame and the stacks of the callees   *)
(* are the region (bot,2856)) and the saved registers, the declassified      *)
(* lists as dc0, ..., dc3, the absorbed states S0, ..., S3, with the streams *)
(* as their bytes, and k0 with its minimality.                               *)
(* ------------------------------------------------------------------------- *)

let ETA_4X_65_INTRO_TAC =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE256X4_INIT_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_INIT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_ABSORB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE256X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_SQUEEZE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_RELEASE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_REJ_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_REJ" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  CONCRETIZE_F_EVENTS_TAC ETA_4X_65_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst ETA_4X_65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

let ETA_4X_65_SETUP_TAC =
  REALIGN_TAC 2887 THEN REALIGN_ALIGNED_TAC [424] THEN
  REALIGN_FRAME_TAC 2935 2887 THEN
  REALIGN_NONOV_TAC 2856
   [`r0:int64,1024`; `r1:int64,1024`; `r2:int64,1024`; `r3:int64,1024`;
    `seed:int64,64`; `word pc:int64,51232`;
    `word_add stackpointer (word 2887):int64,48`;
    `word_add stackpointer (word 2935):int64,32`] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15`;;

let ETA_4X_65_DECLASS_TAC =
  MAP_EVERY (fun (h,d) ->
    ABBREV_TAC(mk_eq(d,eta_4x_65_declass h)))
   (zip ETA_4X_65_NONCES ETA_4X_65_DS);;

let ETA_4X_65_STATES_TAC =
  MAP_EVERY (fun (h,sv) ->
    let t = vsubst [eta_4x_65_input h,`M:num`]
             `mld_keccak_absorb_once 136 0x1F 66 M` in
    ABBREV_TAC(mk_eq(sv,t)) THEN
    ASSUME_TAC(SYM(REWRITE_RULE[ASSUME(mk_eq(t,sv))]
                    (SPECL [`66`; eta_4x_65_input h] mld_shake256_stream))))
   (zip ETA_4X_65_NONCES ETA_4X_65_SVS);;

(*** The count conversions for polynomial m, from its termination ***)

let ETA_4X_65_CNV m (asl,w) =
  let h = el m ETA_4X_65_NONCES and d = el m ETA_4X_65_DS in
  let tth = snd(find (fun (_,th) ->
              concl th = mk_comb(`mld_rej_eta_terminates 4`,
                                 eta_4x_65_stream h)) asl)
  and ath = snd(find (fun (_,th) ->
              concl th = mk_eq(eta_4x_65_declass h,d)) asl) in
  REWRITE_RULE[ath] (MATCH_MP (SPEC `4` MLD_POLY_UNIFORM_ETA_COUNT) tth);;

let ETA_4X_65_MINIMAL_TAC =
  let p = mk_abs(`n:num`,ETA_4X_65_DONE `n:num`) in
  let sumd = end_itlist (mk_binop `(+):num->num->num`)
              (map (fun d -> mk_comb(`LENGTH:bool list->num`,d))
                   ETA_4X_65_DS) in
  MP_TAC(BETA_RULE(fst(EQ_IMP_RULE(ISPEC p MINIMAL)))) THEN
  ANTS_TAC THENL
   [EXISTS_TAC sumd THEN REPEAT CONJ_TAC THEN
    W(fun (asl,w) ->
      let m = index (rand(rand(rand(rand w)))) ETA_4X_65_DS in
      let h = el m ETA_4X_65_NONCES and d = el m ETA_4X_65_DS in
      let tth = snd(find (fun (_,th) ->
              concl th = mk_comb(`mld_rej_eta_terminates 4`,
                                 eta_4x_65_stream h)) asl)
      and ath = snd(find (fun (_,th) ->
              concl th = mk_eq(eta_4x_65_declass h,d)) asl) in
      MATCH_MP_TAC(REWRITE_RULE[ath]
        (MATCH_MP (REWRITE_RULE[IMP_CONJ] (SPEC `4` MLD_POLY_UNIFORM_ETA_DONE))
                  tth)) THEN
      ARITH_TAC);
    ALL_TAC] THEN
  ABBREV_TAC(mk_eq(`k0:num`,mk_comb(`(minimal):(num->bool)->num`,p))) THEN
  STRIP_TAC;;

let ETA_4X_65_MINIMALITY_TAC j =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Const("!",_),Abs(v,Comb(Comb(Const("==>",_),
        Comb(Comb(Const("<",_),v'),Var("k0",_))),_))) when v' = v ->
        MP_TAC(SPEC j th)
    | _ -> NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* The seed as the four 128-bit words that the code loads, the nonces on the *)
(* stack as the 32-bit words that it loads, the 66 bytes of each extended    *)
(* seed with the nonce byte and a zero byte, the states after absorbing, and *)
(* the blocks after squeezing as bytes of the streams (their addresses       *)
(* normalized as in the precondition of mld_rej_eta_c65).                    *)
(* ------------------------------------------------------------------------- *)

let ETA_4X_65_SEED_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes(seed,64)) s = sd`) (concl th)
    then MP_TAC(MATCH_MP (SPEC `4` MLD_READ_BYTES_CHUNKS)
                 (REWRITE_RULE[ARITH_RULE `64 = 16 * 4`] th)) THEN
         MP_TAC(ISPECL [`seed:int64`; `64`; `read memory (s0:x86state)`]
                       READ_BYTES_BOUND) THEN
         REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; ASSUME(concl th)]
    else NO_TAC) THEN
  DISCH_TAC THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  REWRITE_TAC[EXP; DIV_1; WORD_ADD_0] THEN STRIP_TAC;;

let ETA_4X_65_STACKARGS_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (term_match []
             `read (memory :> bytes64 (word_add stackpointer (word k))) s =
              (n:int64)`) (concl th) &&
       is_var(rand(concl th)) &&
       mem (name_of(rand(concl th))) ["n1"; "n2"; "n3"]
    then ASSUME_TAC(MATCH_MP SAMPLING_READ_BYTES32_OF_64 th)
    else NO_TAC));;

let ETA_4X_65_EXTSEED_TAC s m =
  let a = ETA_4X_65_EXT m and h = el m ETA_4X_65_NONCES in
  let t64 = list_mk_comb(`read:((x86state,num)component)->x86state->num`,
             [mk_comb(mk_comb(`(:>):(x86state,int64->byte)component->
                       ((int64->byte),num)component->(x86state,num)component`,
                       `memory`),
                      mk_comb(`bytes:int64#num->((int64->byte),num)component`,
                              mk_pair(a,`64`))); s]) in
  SUBGOAL_THEN (mk_eq(t64,`sd:num`)) ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `64 = 16 * 4`] THEN
    MATCH_MP_TAC MLD_BYTES_OF_CHUNKS THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o check (fun th ->
        can (term_match [] `sd < 2 EXP n`) (concl th))) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      REWRITE_TAC[EXP; DIV_1; WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [a; `sd:num`; h; s] MLD_READ_BYTES66_NONCE8) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[SAMPLING_WORD_ZX_8];
    DISCH_TAC];;

let ETA_4X_65_ABSORBED_TAC =
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

let ETA_4X_65_SHIFT136 =
  REWRITE_RULE[ARITH_RULE `0 < 136`]
   (SPEC `136` MLD_KECCAK_SQUEEZE_BYTE_SHIFT);;

let ETA_4X_65_BLOCKS_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes(a,136 * n)) s =
                           nsum {i | i < n} f`) (concl th)
    then ASSUME_TAC(MATCH_MP MLD_SQUEEZE_BLOCKS_BYTES8
                     (CONJ (ARITH_RULE `0 < 136`) th))
    else NO_TAC)) THEN
  W(fun (asl,w) ->
    let sts = filter (fun th -> can (term_match []
                `mld_keccak_squeeze_byte 136 S 136 = mld_shake256_stream n m`)
                (concl th)) (map snd asl) in
    RULE_ASSUM_TAC(fun th ->
      if can (term_match [] `!j. j < 136 * n ==> P j`) (concl th)
      then CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
            (REWRITE_RULE(ETA_4X_65_SHIFT136::
                          ARITH_RULE `136 * (2 + i) = 272 + 136 * i`::
                          sts) th)
      else th)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_KECCAK_SQUEEZE_ADD;
                              ARITH_RULE `1 + 2 + i = 2 + i + 1`]) THEN
  SAMPLING_BYTES_NORMALIZE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The four first samplings, from the bytes of the first two blocks: the     *)
(* count, the values declassified and the coefficients of each. Each CALL is *)
(* a step of its own, before the step of the callee, and RSP gets the value  *)
(* of the AND after step 8.                                                  *)
(* ------------------------------------------------------------------------- *)

let ETA_4X_65_CALL0_TAC m n =
  let h = el m ETA_4X_65_NONCES and d = el m ETA_4X_65_DS in
  ETA_4X_65_CALL_TAC "H_REJ"
   [`read RDI s`; `0`; `read RDX s`; `272`; eta_4x_65_stream h] n THEN
  W(fun (asl,w) ->
    let tth = snd(find (fun (_,th) ->
                concl th = mk_comb(`mld_rej_eta_terminates 4`,
                                   eta_4x_65_stream h)) asl)
    and ath = snd(find (fun (_,th) ->
                concl th = mk_eq(eta_4x_65_declass h,d)) asl) in
    let dth = REWRITE_RULE[ath] (SPEC `272` (MATCH_MP
                (SPEC `4` MLD_POLY_UNIFORM_ETA_DECLASS_FIRST) tth))
    and cth = SYM(SPEC `2 * 272` (ETA_4X_65_CNV m (asl,w))) in
    RULE_ASSUM_TAC(REWRITE_RULE[dth; MLD_REJ_ETA_CTR_FIRST; cth; LE_0;
                                SUB_0; ARITH_RULE `2 * 272 = 544`]));;

let ETA_4X_65_PART1_TAC =
  FULL_INIT_TAC THEN ETA_4X_65_SEED_TAC THEN ETA_4X_65_STACKARGS_TAC THEN
  SAMPLING_GHOST_REGS_TAC [`YMM0`; `YMM1`; `YMM2`; `YMM3`] "s0" THEN
  X86_STEPS_TAC ETA_4X_65_EXEC (1--8) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC ETA_4X_65_EXEC (9--53) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SAMPLING_SUBWORD_JOIN_128]) THEN
  SAMPLING_NONCE_BYTES_TAC THEN
  MAP_EVERY (ETA_4X_65_EXTSEED_TAC `s53:x86state`) (0--3) THEN
  X86_STEPS_TAC ETA_4X_65_EXEC (54--54) THEN
  ETA_4X_65_CALL_TAC "H_INIT" [`read RDI s`] 55 THEN
  X86_STEPS_TAC ETA_4X_65_EXEC (56--63) THEN
  ETA_4X_65_CALL_TAC "H_ABSORB"
   ([`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `read R8 s`;
     `66`] @ map eta_4x_65_input ETA_4X_65_NONCES) 64 THEN
  ETA_4X_65_ABSORBED_TAC THEN
  X86_STEPS_TAC ETA_4X_65_EXEC (65--78) THEN
  ETA_4X_65_CALL_TAC "H_SQUEEZE"
   ([`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `2`;
     `read R9 s`] @ ETA_4X_65_SVS) 79 THEN
  ETA_4X_65_BLOCKS_TAC THEN
  MAP_EVERY (fun (m,(n1,n2)) ->
    X86_STEPS_TAC ETA_4X_65_EXEC (n1--(n2-1)) THEN
    ETA_4X_65_CALL0_TAC m n2)
   (zip (0--3) [80,85; 86,92; 93,99; 100,106]) THEN
  ARGS_32_TAC (butlast eta_4x_65_cs0) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ETA_4X_65_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The test of the loop, as for mldsa_poly_uniform_4x.                       *)
(* ------------------------------------------------------------------------- *)

let ETA_4X_65_TEST3_TAC cs =
  SAMPLING_COUNT_TEST_TAC cs `~(255 < n0 /\ 255 < n1 /\ 255 < n2)`;;

let ETA_4X_65_TEST1_TAC cs =
  SAMPLING_COUNT_TEST_TAC [last cs] `~(255 < n0)`;;

(*** Rewrite the RIP fact only with th ***)

let ETA_4X_65_RIP_REWRITE_TAC th =
  FIRST_X_ASSUM(fun rth ->
    if can (term_match [] `read RIP s = (x:int64)`) (concl rth)
    then ASSUME_TAC(REWRITE_RULE[th] rth) else NO_TAC);;

let ETA_4X_65_LAST_TAC =
  SUBGOAL_THEN (mk_eq(ETA_4X_65_DONE1 `dc3:bool list` `i + 1`,
                      `~(i + 1 < k0)`))
   ETA_4X_65_RIP_REWRITE_TAC THENL
   [EQ_TAC THENL
     [DISCH_TAC THEN ETA_4X_65_MINIMALITY_TAC `i + 1` THEN
      REWRITE_TAC[ASSUME(ETA_4X_65_DONE3 `i + 1`);
                  ASSUME(ETA_4X_65_DONE1 `dc3:bool list` `i + 1`)];
      DISCH_TAC THEN SUBGOAL_THEN `i + 1 = k0` SUBST1_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`i < k0`; `~(i + 1 < k0)`] THEN ARITH_TAC;
        FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC];;

let ETA_4X_65_NOTLAST_TAC =
  SUBGOAL_THEN `i + 1 < k0` (fun th ->
    ETA_4X_65_RIP_REWRITE_TAC(EQT_INTRO th) THEN ASSUME_TAC th) THENL
   [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `k0 = i + 1` SUBST_ALL_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`i < k0`; `k0 <= i + 1`] THEN ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC(mk_neg(ETA_4X_65_DONE3 `i + 1`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The branch round the loop when no more blocks are needed, and the entry   *)
(* to the loop otherwise, by either path.                                    *)
(* ------------------------------------------------------------------------- *)

let ETA_4X_65_NOLOOP_TAC =
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE ETA_4X_65_ZERO_RULES) THEN
  REWRITE_TAC[] THEN
  FULL_INIT_TAC THEN ABBREV_TAC `rdx0 = read RDX s0` THEN
  X86_STEPS_TAC ETA_4X_65_EXEC (1--11) THEN
  ETA_4X_65_TEST3_TAC eta_4x_65_cs0 THEN
  SUBGOAL_THEN ETA_4X_65_DONE3_0 ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; SAMPLING_CASE_REWRITE_TAC] THEN
  X86_STEPS_TAC ETA_4X_65_EXEC (12--13) THEN
  ETA_4X_65_TEST1_TAC eta_4x_65_cs0 THEN
  SUBGOAL_THEN (ETA_4X_65_DONE1_0 `dc3:bool list`)
   ETA_4X_65_RIP_REWRITE_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY (fun c ->
    SUBGOAL_THEN (mk_eq(c,`256`))
     (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[ARITH_RULE `MIN a b = a <=> a <= b`] THEN ASM_REWRITE_TAC[];
      ALL_TAC]) eta_4x_65_cs0 THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC ETA_4X_65_ZERO_RULES THEN ASM_REWRITE_TAC[] THEN
  ETA_4X_65_DISCHARGE_TAC;;

let ETA_4X_65_LOOP_INIT_TAC =
  FULL_INIT_TAC THEN ABBREV_TAC `rdx0 = read RDX s0` THEN
  X86_STEPS_TAC ETA_4X_65_EXEC (1--11) THEN
  ETA_4X_65_TEST3_TAC eta_4x_65_cs0 THEN
  ARGS_32_TAC [last eta_4x_65_cs0] THEN
  ASM_CASES_TAC ETA_4X_65_DONE3_0 THEN SAMPLING_CASE_REWRITE_TAC THENL
   [X86_STEPS_TAC ETA_4X_65_EXEC (12--13) THEN
    ETA_4X_65_TEST1_TAC eta_4x_65_cs0 THEN
    SUBGOAL_THEN (mk_neg(ETA_4X_65_DONE1_0 `dc3:bool list`))
     ETA_4X_65_RIP_REWRITE_TAC THENL
     [ETA_4X_65_MINIMALITY_TAC `0` THEN
      REWRITE_TAC ETA_4X_65_ZERO_RULES THEN ASM_REWRITE_TAC[] THEN
      ANTS_TAC THENL [UNDISCH_TAC `~(k0 = 0)` THEN ARITH_TAC; REWRITE_TAC[]];
      ALL_TAC];
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC ETA_4X_65_ZERO_RULES THEN ASM_REWRITE_TAC[] THEN
  ETA_4X_65_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The loop body, for iteration i, with the counts before it as c0, ..., c3  *)
(* (their definitions packed into one conjunction, and put back before the   *)
(* events are matched with the template). The call of mld_rej_eta_c65 for    *)
(* polynomial m on the block of the bytes from t = 272 + 136 * i on gets its *)
(* count c, declassifies the part of D from 2 * t on that it reads, and adds *)
(* the coefficients of the block after the count, giving those of the bytes  *)
(* up to t + 136. The count of the fourth is kept in the frame across the    *)
(* call of mldsa_shake256x4_squeezeblocks.                                   *)
(* ------------------------------------------------------------------------- *)

let ETA_4X_65_IS_ABBREV tm =
  match tm with
    Comb(Comb(Const("=",_),Comb(Comb(Const("MIN",_),_),_)),Var(n,_)) ->
      String.length n = 2 && String.sub n 0 1 = "c"
  | _ -> false;;

let ETA_4X_65_ABBREV_TAC =
  MAP_EVERY (fun m ->
    let t = eta_4x_65_count (el m ETA_4X_65_DS) `i:num` in
    ASSUME_TAC(SPECL [`256`; rand t] (ARITH_RULE `!a b. MIN a b <= a`)) THEN
    ABBREV_TAC(mk_eq(mk_var("c"^string_of_int m,`:num`),t))) (0--3) THEN
  (fun (asl,w) ->
    let hs,ks = partition (fun (_,th) -> ETA_4X_65_IS_ABBREV(concl th))
                          asl in
    let cth = end_itlist CONJ (map snd hs) in
    (null_meta,[("",ASSUME(concl cth))::ks,w],
     fun i ths -> PROVE_HYP (INSTANTIATE_ALL i cth) (hd ths)));;

let ETA_4X_65_ABBREV m =
  let eq = mk_eq(eta_4x_65_count (el m ETA_4X_65_DS) `i:num`,
                 mk_var("c"^string_of_int m,`:num`)) in
  fun (asl,w) ->
    tryfind (fun (_,th) -> find (fun th' -> concl th' = eq) (CONJUNCTS th))
            asl;;

let ETA_4X_65_UNABBREV_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_conj(concl th) && ETA_4X_65_IS_ABBREV(lhand(concl th))
    then MAP_EVERY (SUBST_ALL_TAC o SYM) (CONJUNCTS th) else NO_TAC);;

let ETA_4X_65_COMBINE_TAC m n =
  let h = el m ETA_4X_65_NONCES and d = el m ETA_4X_65_DS
  and vec = el m ETA_4X_65_VECS in
  let c = mk_var("c"^string_of_int m,`:num`)
  and s = mk_var("s"^string_of_int n,`:x86state`) in
  let strm = eta_4x_65_stream h in
  let goal = vsubst [vec,`vec:int64`; strm,`str:num->byte`; s,`s:x86state`;
                     d,`D:bool list`]
   `!k. k < MIN 256 (LENGTH(FILTER (\x:bool. x)
                    (SUB_LIST(0,2 * (272 + 136 * (i + 1))) D)))
        ==> read (memory :> bytes32(word_add vec (word(4 * k)))) s =
            EL k (mld_rej_eta_list 4 str (2 * (272 + 136 * (i + 1))))` in
  let isvecfact pat th =
    is_forall(concl th) && free_in vec (concl th) && free_in s (concl th) &&
    can (term_match [] pat) (concl th) in
  W(fun gl ->
    let ath = ETA_4X_65_ABBREV m gl and cnv = ETA_4X_65_CNV m gl in
    let tth = snd(find (fun (_,th) ->
                concl th = mk_comb(`mld_rej_eta_terminates 4`,strm)) (fst gl))
    and dath = snd(find (fun (_,th) ->
                concl th = mk_eq(eta_4x_65_declass h,d)) (fst gl)) in
    let sc = TRANS (SYM(SPEC `2 * (272 + 136 * i)` cnv)) ath in
    let cth = REWRITE_RULE[ARITH_RULE
                `(272 + 136 * i) + 136 = 272 + 136 * (i + 1)`;
                GSYM(SPEC `2 * (272 + 136 * (i + 1))` cnv)]
               (SPEC `136` (MATCH_MP (SPEC `4` MLD_REJ_ETA_CTR_BLOCK) sc))
    and dth = REWRITE_RULE[dath]
               (SPEC `136` (MATCH_MP
                 (SPEC `4` MLD_POLY_UNIFORM_ETA_DECLASS_BLOCK)
                 (CONJ tth sc))) in
    RULE_ASSUM_TAC(REWRITE_RULE[cth; dth]) THEN
    SUBGOAL_THEN goal ASSUME_TAC THENL
     [X_GEN_TAC `k:num` THEN
      REWRITE_TAC[cnv] THEN DISCH_TAC THEN
      MP_TAC(SPECL [`4`; strm; `272 + 136 * i`; c; `136`; `k:num`]
                   MLD_REJ_ETA_EL_BLOCK) THEN
      REWRITE_TAC[ARITH_RULE `(272 + 136 * i) + 136 = 272 + 136 * (i + 1)`]
      THEN ANTS_TAC THENL [ASM_REWRITE_TAC[sc]; DISCH_THEN SUBST1_TAC] THEN
      COND_CASES_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check
          (isvecfact `!k. k < c ==> P k`)) THEN
        ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o check
          (isvecfact `!k. c <= k /\ k < d ==> P k`)) THEN
        ASM_REWRITE_TAC[GSYM NOT_LT; cnv]];
      ALL_TAC]);;

let ETA_4X_65_CALL1_TAC m n =
  let h = el m ETA_4X_65_NONCES in
  let c = mk_var("c"^string_of_int m,`:num`) in
  let b = mk_abs(`j:num`,
           mk_comb(eta_4x_65_stream h,`(272 + 136 * i) + j`)) in
  ARGS_32_TAC [c] THEN
  ETA_4X_65_CALL_TAC "H_REJ"
   [`read RDI s`; c; `read RDX s`; `136`; b] n THEN
  ETA_4X_65_COMBINE_TAC m n;;

let ETA_4X_65_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  ETA_4X_65_ABBREV_TAC THEN
  FULL_INIT_TAC THEN

  (*** Squeezing one more block from each state ***)

  X86_STEPS_TAC ETA_4X_65_EXEC (1--8) THEN
  ETA_4X_65_CALL_TAC "H_SQUEEZE"
   ([`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `1`;
     `read R9 s`] @
    map (fun sv -> mk_comb(`keccak_squeeze (2 + i)`,sv)) ETA_4X_65_SVS) 9
  THEN
  ETA_4X_65_BLOCKS_TAC THEN

  (*** Sampling from each block after the coefficients so far ***)

  MAP_EVERY (fun (m,(n1,n2)) ->
    X86_STEPS_TAC ETA_4X_65_EXEC (n1--(n2-1)) THEN
    ETA_4X_65_CALL1_TAC m n2)
   (zip (0--3) [10,15; 16,22; 23,29; 30,36]) THEN

  (*** The test of whether all four have 256 coefficients now ***)

  ARGS_32_TAC eta_4x_65_cs1 THEN
  ABBREV_TAC `rdx0 = read RDX s36` THEN
  X86_STEPS_TAC ETA_4X_65_EXEC (37--46) THEN
  ETA_4X_65_TEST3_TAC eta_4x_65_cs1 THEN
  ASM_CASES_TAC (ETA_4X_65_DONE3 `i + 1`) THEN
  SAMPLING_CASE_REWRITE_TAC THENL
   [X86_STEPS_TAC ETA_4X_65_EXEC (47--48) THEN
    ETA_4X_65_TEST1_TAC eta_4x_65_cs1 THEN
    ETA_4X_65_LAST_TAC;
    ETA_4X_65_NOTLAST_TAC] THEN
  ARGS_32_TAC eta_4x_65_cs1 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(CONJ_TAC THENL
       [COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC; ALL_TAC]) THEN
  ETA_4X_65_UNABBREV_TAC THEN ETA_4X_65_DISCHARGE_TAC;;

(*** The exit of the loop, where all four have 256 coefficients ***)

let ETA_4X_65_EXIT_TAC =
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  MAP_EVERY (fun d ->
    SUBGOAL_THEN (mk_eq(eta_4x_65_count d `k0:num`,`256`))
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC]) ETA_4X_65_DS THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ETA_4X_65_DISCHARGE_TAC;;

let ETA_4X_65_LOOP_TAC =
  REWRITE_TAC[EQF_INTRO(ASSUME `~(k0 = 0)`)] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `k0:num`
   `pc + mldsa65_poly_uniform_eta_4x_join1`
   ETA_4X_65_EXIT ETA_4X_65_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ETA_4X_65_LOOP_INIT_TAC;
    ETA_4X_65_BODY_TAC;
    ETA_4X_65_EXIT_TAC];;

(* ------------------------------------------------------------------------- *)
(* Releasing the state, zeroing the buffers and the extended seeds (REP      *)
(* STOSQs of 144 and 48 quadwords) and the return, with the polynomials as   *)
(* mld_poly_uniform_eta.                                                     *)
(* ------------------------------------------------------------------------- *)

let ETA_4X_65_RESULTS_TAC =
  MAP_EVERY (fun (h,(d,vec)) ->
    SUBGOAL_THEN
     (vsubst [h,`h:byte`; vec,`vec:int64`]
       `!k. k < 256
            ==> read (memory :> bytes32(word_add vec (word(4 * k)))) s0 =
                mld_poly_uniform_eta 4 sd h k`)
     ASSUME_TAC THENL
     [MATCH_MP_TAC ETA_4X_65_RESULT THEN
      MAP_EVERY EXISTS_TAC [d; `k0:num`] THEN ASM_REWRITE_TAC[];
      ALL_TAC])
   (zip ETA_4X_65_NONCES (zip ETA_4X_65_DS ETA_4X_65_VECS));;

let ETA_4X_65_PART3_TAC =
  FULL_INIT_TAC THEN ETA_4X_65_RESULTS_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `k0:num`)) THEN
  X86_STEPS_TAC ETA_4X_65_EXEC (1--2) THEN
  ETA_4X_65_CALL_TAC "H_RELEASE" [`read RDI s`] 3 THEN
  X86_STEPS_TAC ETA_4X_65_EXEC (4--19) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ETA_4X_65_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together.                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  ETA_4X_65_INTRO_TAC THEN ETA_4X_65_SETUP_TAC THEN
  ETA_4X_65_DECLASS_TAC THEN ETA_4X_65_STATES_TAC THEN
  ETA_4X_65_MINIMAL_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC ETA_4X_65_EXIT
   ETA_4X_65_A2 THEN CONJ_TAC THENL
   [ENSURES_EVENTS_SEQUENCE_TAC
     `pc + mldsa65_poly_uniform_eta_4x_after_mld_rej_eta_c65_4`
     ETA_4X_65_A1 THEN CONJ_TAC THENL
     [ETA_4X_65_PART1_TAC;
      ASM_CASES_TAC `k0 = 0` THENL
       [ETA_4X_65_NOLOOP_TAC; ETA_4X_65_LOOP_TAC]];
    ETA_4X_65_PART3_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
