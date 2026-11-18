(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling of four polynomials with coefficients in [-2,2] for ML-DSA-87:   *)
(* the proof (see poly_uniform_eta_4x_87_spec.ml). It follows the proof for  *)
(* mldsa_poly_uniform_4x, with the extended seeds of                         *)
(* mldsa87_poly_uniform_gamma1_4x, except that the events may depend on the  *)
(* seed only through the lists dc0, ..., dc3 of the values that the calls of *)
(* mld_rej_eta_c87 declassify: the counts of coefficients, on which the loop *)
(* test branches and which the calls get, are numbers of T in initial        *)
(* segments of these lists, and the values that a call declassifies are a    *)
(* sublist.                                                                  *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/poly_uniform_eta_4x_87_spec.ml";;
needs "arm/proofs/utils/mldsa_native_sampling.ml";;

let ETA_4X_87_EXEC = MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The nonces, the inputs and outputs of SHAKE256, the declassified lists    *)
(* dc0 to dc3, the absorbed states, and the count of coefficients of each    *)
(* after t blocks after the first one (136 bytes), as a number of T in D.    *)
(* ------------------------------------------------------------------------- *)

let ETA_4X_87_NONCES =
  [`word_zx(n0:int64):byte`; `word_zx(n1:int64):byte`;
   `word_zx(n2:int64):byte`; `n3:byte`]
and ETA_4X_87_DS =
  [`dc0:bool list`; `dc1:bool list`; `dc2:bool list`; `dc3:bool list`]
and ETA_4X_87_VECS = [`r0:int64`; `r1:int64`; `r2:int64`; `r3:int64`]
and ETA_4X_87_SVS =
  [`S0:1600 word`; `S1:1600 word`; `S2:1600 word`; `S3:1600 word`];;

let eta_4x_87_input h = vsubst [h,`h:byte`] `sd + 2 EXP 512 * val(h:byte)`;;

let eta_4x_87_stream h =
  mk_comb(`mld_shake256_stream 66`,eta_4x_87_input h);;

let eta_4x_87_declass h =
  mk_comb(`mld_poly_uniform_eta_declass 2`,eta_4x_87_stream h);;

let eta_4x_87_groups t =
  mk_binop `(+):num->num->num` `136`
   (mk_binop `( * ):num->num->num` `136` t);;

let eta_4x_87_count d t =
  vsubst [d,`D:bool list`; eta_4x_87_groups t,`n:num`]
   `MIN 256 (LENGTH(FILTER (\x:bool. x) (SUB_LIST(0,2 * n) D)))`;;

let ETA_4X_87_ZERO_RULES =
  [MULT_CLAUSES; ADD_CLAUSES; ARITH_RULE `2 * 136 = 272`];;

let eta_4x_87_count0 d =
  rhs(concl(REWRITE_CONV ETA_4X_87_ZERO_RULES (eta_4x_87_count d `0`)));;

let eta_4x_87_cs0 = map eta_4x_87_count0 ETA_4X_87_DS
and eta_4x_87_cs1 = map (fun d -> eta_4x_87_count d `i + 1`) ETA_4X_87_DS;;

let ETA_4X_87_DONE n =
  list_mk_conj
   (map (fun d -> vsubst [d,`D:bool list`; eta_4x_87_groups n,`n:num`]
                   `256 <= LENGTH(FILTER (\x:bool. x) (SUB_LIST(0,2 * n) D))`)
        ETA_4X_87_DS);;

(* ------------------------------------------------------------------------- *)
(* The events, as for mldsa_poly_uniform_4x, with the loop over the k0 more  *)
(* blocks that are needed, k0 being now a function of dc0, ..., dc3.         *)
(* ------------------------------------------------------------------------- *)

let ETA_4X_87_TEMPLATE =
  let args = [`r0:int64`; `r1:int64`; `r2:int64`; `r3:int64`;
              `seed:int64`; `dc0:bool list`; `dc1:bool list`; `dc2:bool list`;
              `dc3:bool list`; `guard:int64`; `mf:int64`; `pc:num`;
              `stackpointer:int64`; `returnaddress:int64`] in
  let fty = itlist (fun a t -> mk_fun_ty (type_of a) t) args
                   `:(uarch_event)list` in
  let fv n = mk_var(n,fty) in
  let app n = list_mk_comb(fv n,args) in
  let k0 = mk_comb(`(minimal):(num->bool)->num`,
                   mk_abs(`n:num`,ETA_4X_87_DONE `n:num`)) in
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

let ETA_4X_87_ALLOWED =
  [`pc:num`; `r0:int64`; `r1:int64`; `r2:int64`; `r3:int64`;
   `seed:int64`; `dc0:bool list`; `dc1:bool list`; `dc2:bool list`;
   `dc3:bool list`; `guard:int64`; `mf:int64`; `stackpointer:int64`;
   `returnaddress:int64`; `i:num`; `c0:num`; `c1:num`; `c2:num`; `c3:num`;
   `f_ev_loop:int64->int64->int64->int64->int64->bool list->bool list->
              bool list->bool list->int64->int64->num->int64->int64->
              num->(uarch_event)list`];;

let ETA_4X_87_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc ETA_4X_87_EXEC name
    ilist ETA_4X_87_ALLOWED n;;

(* ------------------------------------------------------------------------- *)
(* The four buffers of 160 bytes for one block each, followed by the four    *)
(* extended seeds of 96 bytes, are aligned to 32 bytes within the stack      *)
(* frame; the four states follow, at a fixed offset.                         *)
(* ------------------------------------------------------------------------- *)

let ETA_4X_87_BUFFER_ADDRESS = SAMPLING_ALIGN32_RULE 479;;

let ETA_4X_87_BOFF = `if aligned 32 (stackpointer:int64) then 448 else 464`;;

let ETA_4X_87_AT k =
  let off = if k = 0 then ETA_4X_87_BOFF
            else mk_binop `(+):num->num->num` ETA_4X_87_BOFF
                          (mk_small_numeral k) in
  mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
          mk_comb(`word:num->int64`,off));;

let ETA_4X_87_EXT m = ETA_4X_87_AT(640 + 96 * m);;

let ETA_4X_87_ST m =
  mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
          mk_comb(`word:num->int64`,mk_small_numeral(1496 + 200 * m)));;

let ETA_4X_87_BUFFER_TAC =
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 479))
             (word 18446744073709551584):int64 =
    word_add stackpointer (word(if aligned 32 stackpointer then 448 else 464))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC ETA_4X_87_BUFFER_ADDRESS THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

let ETA_4X_87_NORMALIZE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th
    else th);;

(*** The GOT entries in the form in the preconditions of the callees ***)

let ETA_4X_87_GOT_TAC =
  MAP_EVERY (fun n ->
    FIRST_ASSUM(fun th ->
      if can (term_match []
               (vsubst [n,`n:num`]
                 `read (memory :> bytes64
                         (word_add (word (pc:num)) (word n):int64)) s =
                  (g:int64)`)) (concl th)
      then ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD] th) else NO_TAC))
   [`got_stack_chk_guard:num`; `got_memset:num`];;

(* ------------------------------------------------------------------------- *)
(* The facts at the intermediate points: the saved registers and arguments,  *)
(* the stack guard, the GOT entries and the region that memset may read, the *)
(* addresses of the buffers and states, and for each polynomial its count,   *)
(* the coefficients so far and its state; at the exit of the loop the        *)
(* polynomials are complete.                                                 *)
(* ------------------------------------------------------------------------- *)

let ETA_4X_87_FRAME =
 `read SP s = word_add stackpointer (word 304) /\
  read (memory :> bytes64 (word_add stackpointer (word 304))) s = x19_init /\
  read (memory :> bytes64 (word_add stackpointer (word 312))) s = x20_init /\
  read (memory :> bytes64 (word_add stackpointer (word 320))) s = x21_init /\
  read (memory :> bytes64 (word_add stackpointer (word 328))) s = x22_init /\
  read (memory :> bytes64 (word_add stackpointer (word 336))) s = x23_init /\
  read (memory :> bytes64 (word_add stackpointer (word 344))) s = x24_init /\
  read (memory :> bytes64 (word_add stackpointer (word 352))) s = x25_init /\
  read (memory :> bytes64 (word_add stackpointer (word 360))) s = x26_init /\
  read (memory :> bytes64 (word_add stackpointer (word 368))) s = x27_init /\
  read (memory :> bytes64 (word_add stackpointer (word 376))) s = x28_init /\
  read (memory :> bytes64 (word_add stackpointer (word 384))) s =
  returnaddress /\
  read (memory :> bytes64 (word_add stackpointer (word 408))) s = r0 /\
  read (memory :> bytes64 (word_add stackpointer (word 416))) s = r1 /\
  read (memory :> bytes64 (word_add stackpointer (word 424))) s = r2 /\
  read (memory :> bytes64 (word_add stackpointer (word 432))) s = r3 /\
  read (memory :> bytes64 (word_add stackpointer (word 440))) s =
  word_add stackpointer
   (word((if aligned 32 stackpointer then 448 else 464) + 640)) /\
  read (memory :> bytes64 (word_add stackpointer (word 2296))) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard))) s =
  guard /\
  read (memory :> bytes64 guard) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word got_memset))) s = mf /\
  read (memory :> bytes(ea,el)) s = ev /\
  read X22 s =
  word_add stackpointer (word(if aligned 32 stackpointer then 448 else 464)) /\
  read X25 s =
  word_add stackpointer
   (word((if aligned 32 stackpointer then 448 else 464) + 160)) /\
  read X24 s =
  word_add stackpointer
   (word((if aligned 32 stackpointer then 448 else 464) + 320)) /\
  read X23 s =
  word_add stackpointer
   (word((if aligned 32 stackpointer then 448 else 464) + 480)) /\
  read X26 s = word_add stackpointer (word 1496) /\
  read X27 s = word 255`;;

let ETA_4X_87_POLY =
 `read (R:(armstate,int64)component) s =
  word(MIN 256 (LENGTH(FILTER (\x:bool. x)
                        (SUB_LIST(0,2 * (136 + 136 * i)) D)))) /\
  (!k. k < MIN 256 (LENGTH(FILTER (\x:bool. x)
                            (SUB_LIST(0,2 * (136 + 136 * i)) D)))
       ==> read (memory :> bytes32(word_add vec (word(4 * k)))) s =
           EL k (mld_rej_eta_list 2 str (2 * (136 + 136 * i)))) /\
  read (memory :> bytes(st,200)) s =
  val(keccak_squeeze (1 + i) (S:1600 word))`;;

let ETA_4X_87_POLYS regs =
  flat
   (map (fun (r,(vec,(h,(d,(st,sv))))) ->
          conjuncts
           (vsubst [r,`R:(armstate,int64)component`; vec,`vec:int64`;
                    d,`D:bool list`; eta_4x_87_stream h,`str:num->byte`;
                    st,`st:int64`; sv,`S:1600 word`]
                   ETA_4X_87_POLY))
        (zip regs (zip ETA_4X_87_VECS (zip ETA_4X_87_NONCES
           (zip ETA_4X_87_DS (zip (map ETA_4X_87_ST (0--3))
                                  ETA_4X_87_SVS))))));;

let ETA_4X_87_A1 =
  let t = vsubst [`0`,`i:num`]
           (list_mk_conj(ETA_4X_87_POLYS [`X19`; `X20`; `X21`; `X0`])) in
  let t' = rhs(concl(REWRITE_CONV ETA_4X_87_ZERO_RULES t)) in
  mk_abs(`s:armstate`,
         list_mk_conj(conjuncts t' @ conjuncts ETA_4X_87_FRAME));;

let ETA_4X_87_INV =
  list_mk_abs([`i:num`; `s:armstate`],
    list_mk_conj(ETA_4X_87_POLYS [`X19`; `X20`; `X21`; `X28`] @
                 conjuncts ETA_4X_87_FRAME));;

let ETA_4X_87_A2 =
  let res h vec =
    vsubst [eta_4x_87_stream h,`str:num->byte`; vec,`vec:int64`]
     `!k. k < 256
          ==> read (memory :> bytes32(word_add vec (word(4 * k)))) s =
              EL k (mld_rej_eta_list 2 str (2 * (136 + 136 * k0)))` in
  mk_abs(`s:armstate`,
    list_mk_conj(map2 res ETA_4X_87_NONCES ETA_4X_87_VECS @
                 conjuncts ETA_4X_87_FRAME));;

(*** The result for one polynomial from the first 136 + 136 * k0 bytes ***)

let ETA_4X_87_RESULT = prove
 (`!vec:int64 sd (h:byte) D k0 (s:armstate).
     mld_rej_eta_terminates 2 (mld_shake256_stream 66 (sd + 2 EXP 512 * val h))
     /\
     mld_poly_uniform_eta_declass 2
      (mld_shake256_stream 66 (sd + 2 EXP 512 * val h)) = D /\
     256 <= LENGTH(FILTER (\x. x) (SUB_LIST(0,2 * (136 + 136 * k0)) D)) /\
     (!k. k < 256
          ==> read (memory :> bytes32(word_add vec (word(4 * k)))) s =
              EL k (mld_rej_eta_list 2
                     (mld_shake256_stream 66 (sd + 2 EXP 512 * val h))
                     (2 * (136 + 136 * k0))))
     ==> (!k. k < 256
              ==> read (memory :> bytes32(word_add vec (word(4 * k)))) s =
                  mld_poly_uniform_eta 2 sd h k)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `D:bool list`)) THEN
  ASM_SIMP_TAC[mld_poly_uniform_eta] THEN
  MATCH_MP_TAC(REWRITE_RULE[ARITH_EQ; ARITH_RULE
    `2 * 136 * (1 + k) = 2 * (136 + 136 * k)`]
   (SPEC `2` MLD_REJ_ETA_POLY_EQ)) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPEC `2 * (136 + 136 * k0)` o
    MATCH_MP (SPEC `2` MLD_POLY_UNIFORM_ETA_COUNT)) THEN
  UNDISCH_TAC
   `256 <= LENGTH(FILTER (\x. x) (SUB_LIST(0,2 * (136 + 136 * k0))
     (mld_poly_uniform_eta_declass 2
       (mld_shake256_stream 66 (sd + 2 EXP 512 * val(h:byte))))))` THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The setup: the callee theorems, the template, the stack frame and the     *)
(* saved registers, the stack guard as canary, the declassified lists as     *)
(* dc0, ..., dc3, the absorbed states S0, ..., S3, with the streams as their *)
(* bytes, and k0 with its minimality.                                        *)
(* ------------------------------------------------------------------------- *)

let ETA_4X_87_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_FULL
               th) "H_RELEASE" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP
       MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_FULL th)
     "H_ABSORB") THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] th)
     "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE256X4_INIT_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_INIT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE256X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_SQUEEZE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_REJ_ETA_87_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_REJ" THEN
  CONCRETIZE_F_EVENTS_TAC ETA_4X_87_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst ETA_4X_87_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

let ETA_4X_87_SETUP_TAC =
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 2304):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `448 <= (if aligned 32 (stackpointer:int64) then 448 else 464) /\
    (if aligned 32 (stackpointer:int64) then 448 else 464) <= 464`
  STRIP_ASSUME_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memset:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    let r = "X"^string_of_int n in
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (mk_const(r,[]))) (19--28);;

let ETA_4X_87_DECLASS_TAC =
  MAP_EVERY (fun (h,d) ->
    ABBREV_TAC(mk_eq(d,eta_4x_87_declass h)))
   (zip ETA_4X_87_NONCES ETA_4X_87_DS);;

let ETA_4X_87_STATES_TAC =
  MAP_EVERY (fun (h,sv) ->
    let t = vsubst [eta_4x_87_input h,`M:num`]
             `mld_keccak_absorb_once 136 0x1F 66 M` in
    ABBREV_TAC(mk_eq(sv,t)) THEN
    ASSUME_TAC(SYM(REWRITE_RULE[ASSUME(mk_eq(t,sv))]
                    (SPECL [`66`; eta_4x_87_input h] mld_shake256_stream))))
   (zip ETA_4X_87_NONCES ETA_4X_87_SVS);;

(*** The count conversions for polynomial m, from its termination ***)

let ETA_4X_87_CNV m (asl,w) =
  let h = el m ETA_4X_87_NONCES and d = el m ETA_4X_87_DS in
  let tth = snd(find (fun (_,th) ->
              concl th = mk_comb(`mld_rej_eta_terminates 2`,
                                 eta_4x_87_stream h)) asl)
  and ath = snd(find (fun (_,th) ->
              concl th = mk_eq(eta_4x_87_declass h,d)) asl) in
  REWRITE_RULE[ath] (MATCH_MP (SPEC `2` MLD_POLY_UNIFORM_ETA_COUNT) tth);;

let ETA_4X_87_MINIMAL_TAC =
  let p = mk_abs(`n:num`,ETA_4X_87_DONE `n:num`) in
  let sumd = end_itlist (mk_binop `(+):num->num->num`)
              (map (fun d -> mk_comb(`LENGTH:bool list->num`,d))
                   ETA_4X_87_DS) in
  MP_TAC(BETA_RULE(fst(EQ_IMP_RULE(ISPEC p MINIMAL)))) THEN
  ANTS_TAC THENL
   [EXISTS_TAC sumd THEN REPEAT CONJ_TAC THEN
    W(fun (asl,w) ->
      let m = index (rand(rand(rand(rand w)))) ETA_4X_87_DS in
      let h = el m ETA_4X_87_NONCES and d = el m ETA_4X_87_DS in
      let tth = snd(find (fun (_,th) ->
              concl th = mk_comb(`mld_rej_eta_terminates 2`,
                                 eta_4x_87_stream h)) asl)
      and ath = snd(find (fun (_,th) ->
              concl th = mk_eq(eta_4x_87_declass h,d)) asl) in
      MATCH_MP_TAC(REWRITE_RULE[ath]
        (MATCH_MP (REWRITE_RULE[IMP_CONJ] (SPEC `2` MLD_POLY_UNIFORM_ETA_DONE))
                  tth)) THEN
      ARITH_TAC);
    ALL_TAC] THEN
  ABBREV_TAC(mk_eq(`k0:num`,mk_comb(`(minimal):(num->bool)->num`,p))) THEN
  STRIP_TAC;;

let ETA_4X_87_MINIMALITY_TAC j =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Const("!",_),Abs(v,Comb(Comb(Const("==>",_),
        Comb(Comb(Const("<",_),v'),Var("k0",_))),_))) when v' = v ->
        MP_TAC(SPEC j th)
    | _ -> NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* The seed as the four 128-bit words that the code loads, the 66 bytes of   *)
(* each extended seed with the nonce byte and a zero byte, the states after  *)
(* absorbing, the blocks after squeezing as bytes of the streams, and counts *)
(* as 32-bit arguments.                                                      *)
(* ------------------------------------------------------------------------- *)

let ETA_4X_87_SEED_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes(seed,64)) s = sd`) (concl th)
    then MP_TAC(MATCH_MP (SPEC `4` MLD_READ_BYTES_CHUNKS)
                 (REWRITE_RULE[ARITH_RULE `64 = 16 * 4`] th)) THEN
         MP_TAC(ISPECL [`seed:int64`; `64`; `read memory (s0:armstate)`]
                       READ_BYTES_BOUND) THEN
         REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; ASSUME(concl th)]
    else NO_TAC) THEN
  DISCH_TAC THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  REWRITE_TAC[EXP; DIV_1; WORD_ADD_0] THEN STRIP_TAC;;

let ETA_4X_87_EXTSEED_TAC s m =
  let a = ETA_4X_87_EXT m and h = el m ETA_4X_87_NONCES in
  let t64 = list_mk_comb(`read:((armstate,num)component)->armstate->num`,
             [mk_comb(mk_comb(`(:>):(armstate,int64->byte)component->
                       ((int64->byte),num)component->(armstate,num)component`,
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

let ETA_4X_87_ABSORBED_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM MLD_KECCAK_ABSORB_ONCE]) THEN
  W(fun (asl,w) ->
    let abs = filter (fun th -> can (term_match []
                `mld_keccak_absorb_once r p n m = (S:1600 word)`) (concl th))
               (map snd asl) in
    RULE_ASSUM_TAC(fun th ->
      if can (term_match [] `read (memory :> wbytes a) s = (x:1600 word)`)
             (concl th)
      then REWRITE_RULE abs th else th));;

let ETA_4X_87_SHIFT136 =
  REWRITE_RULE[ARITH_RULE `0 < 136`]
   (SPEC `136` MLD_KECCAK_SQUEEZE_BYTE_SHIFT);;

let ETA_4X_87_BLOCKS_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
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
            (REWRITE_RULE(ETA_4X_87_SHIFT136::
                          ARITH_RULE `136 * (1 + i) = 136 + 136 * i`::
                          sts) th)
      else th)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_KECCAK_SQUEEZE_ADD;
                              ARITH_RULE `1 + 1 + i = 1 + i + 1`]) THEN
  ETA_4X_87_NORMALIZE_TAC;;

let ETA_4X_87_ARGS_32_TAC c =
  MP_TAC(SPEC c WORD_ZX_32_SMALL) THEN
  ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN
    (ARITH_TAC ORELSE
     FIRST_ASSUM(fun th ->
      if (is_binary "<" (concl th) || is_binary "<=" (concl th)) &&
         lhand(concl th) = c
      then MP_TAC th THEN ARITH_TAC else NO_TAC));
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))];;

(* ------------------------------------------------------------------------- *)
(* The four first samplings, from the bytes of the first block: the count,   *)
(* the values declassified and the coefficients of each.                     *)
(* ------------------------------------------------------------------------- *)

let ETA_4X_87_CALL0_TAC m n =
  let h = el m ETA_4X_87_NONCES and d = el m ETA_4X_87_DS in
  ETA_4X_87_CALL_TAC "H_REJ"
   [`read X0 s`; `0`; `read X2 s`; eta_4x_87_stream h; `pc:num`;
    `read X30 s`] n THEN
  W(fun (asl,w) ->
    let tth = snd(find (fun (_,th) ->
                concl th = mk_comb(`mld_rej_eta_terminates 2`,
                                   eta_4x_87_stream h)) asl)
    and ath = snd(find (fun (_,th) ->
                concl th = mk_eq(eta_4x_87_declass h,d)) asl) in
    let dth = REWRITE_RULE[ath] (SPEC `136` (MATCH_MP
                (SPEC `2` MLD_POLY_UNIFORM_ETA_DECLASS_FIRST) tth))
    and cth = SYM(SPEC `2 * 136` (ETA_4X_87_CNV m (asl,w))) in
    RULE_ASSUM_TAC(REWRITE_RULE[dth; MLD_REJ_ETA_CTR_FIRST; cth; LE_0;
                                SUB_0; ARITH_RULE `2 * 136 = 272`]));;

let ETA_4X_87_PART1_TAC =
  FULL_INIT_TAC THEN ETA_4X_87_SEED_TAC THEN
  ARM_STEPS_TAC ETA_4X_87_EXEC (1--3) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC ETA_4X_87_EXEC (4--8) THEN ETA_4X_87_BUFFER_TAC THEN
  ARM_STEPS_TAC ETA_4X_87_EXEC (9--49) THEN ETA_4X_87_NORMALIZE_TAC THEN
  MAP_EVERY (ETA_4X_87_EXTSEED_TAC `s49:armstate`) (0--3) THEN
  ETA_4X_87_CALL_TAC "H_INIT" [`read X0 s`; `pc:num`; `read X30 s`] 50
  THEN
  ARM_STEPS_TAC ETA_4X_87_EXEC (51--57) THEN ETA_4X_87_GOT_TAC THEN
  ETA_4X_87_CALL_TAC "H_ABSORB"
   ([`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
     `66`] @ map eta_4x_87_input ETA_4X_87_NONCES @
    [`guard:int64`; `pc:num`; `read SP s`; `read X30 s`]) 58 THEN
  ETA_4X_87_ABSORBED_TAC THEN
  ARM_STEPS_TAC ETA_4X_87_EXEC (59--65) THEN
  ETA_4X_87_CALL_TAC "H_SQUEEZE"
   ([`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `1`;
     `read X5 s`] @ ETA_4X_87_SVS @
    [`pc:num`; `read SP s`; `read X30 s`]) 66 THEN
  ETA_4X_87_BLOCKS_TAC THEN
  MAP_EVERY (fun (m,k) ->
    ARM_STEPS_TAC ETA_4X_87_EXEC (k--(70 + 6 * m)) THEN
    ETA_4X_87_CALL0_TAC m (71 + 6 * m)) [0,67; 1,72; 2,78; 3,84] THEN
  MAP_EVERY ETA_4X_87_ARGS_32_TAC (butlast eta_4x_87_cs0) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* The loop test, as for mldsa_poly_uniform_4x.                              *)
(* ------------------------------------------------------------------------- *)

let ETA_4X_87_CMP = prove
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

let ETA_4X_87_TEST_PROVE_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `n0 < 2 EXP 32 /\ n1 < 2 EXP 32 /\ n2 < 2 EXP 32 /\ n3 < 2 EXP 32`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[ETA_4X_87_CMP] THEN
  REWRITE_TAC[TAUT `(if a then b else F) <=> a /\ b`;
              ARITH_RULE `255 <= n /\ ~(n = 255) <=> 255 < n`] THEN
  REPEAT COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV THEN ASM_ARITH_TAC;;

let ETA_4X_87_TEST_TAC cs =
  let vs = map (fun i -> mk_var("n"^string_of_int i,`:num`)) (0--3) in
  let ant = list_mk_conj
             (map (fun v -> mk_binop `(<=):num->num->bool` v `256`) vs)
  and res = list_mk_conj
             (map (fun v -> mk_binop `(<):num->num->bool` `255` v) vs) in
  let bth = end_itlist CONJ
             (map (fun c -> SPECL [`256`; rand c]
                    (ARITH_RULE `!a b. MIN a b <= a`)) cs) in
  FIRST_X_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),_)),
           Comb(Comb(Comb(Const("COND",_),c),_),_)) when free_in (hd cs) c ->
        let res' = if is_neg c then mk_neg res else res in
        let lth = prove(list_mk_forall(vs,mk_imp(ant,mk_eq(subst(zip vs cs) c,
                                                          res'))),
                        ETA_4X_87_TEST_PROVE_TAC) in
        ASSUME_TAC(REWRITE_RULE[MP (SPECL cs lth) bth;
                                ARITH_RULE `255 < MIN 256 x <=> 256 <= x`] th)
    | _ -> NO_TAC);;

let ETA_4X_87_LS_TAC =
  SUBGOAL_THEN (mk_eq(ETA_4X_87_DONE `i + 1`,`~(i + 1 < k0)`))
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [EQ_TAC THENL
     [DISCH_THEN(fun dth -> DISCH_THEN(fun lth ->
        ETA_4X_87_MINIMALITY_TAC `i + 1` THEN REWRITE_TAC[dth; lth]));
      DISCH_TAC THEN SUBGOAL_THEN `i + 1 = k0` SUBST1_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`i < k0`; `~(i + 1 < k0)`] THEN ARITH_TAC;
        REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The branch round the loop when no more blocks are needed, and the entry   *)
(* to the loop otherwise.                                                    *)
(* ------------------------------------------------------------------------- *)

let ETA_4X_87_NOLOOP_TAC =
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE ETA_4X_87_ZERO_RULES) THEN
  REWRITE_TAC[] THEN
  MAP_EVERY (fun c ->
    SUBGOAL_THEN (mk_eq(c,`256`))
     (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[ARITH_RULE `MIN a b = a <=> a <= b`] THEN ASM_REWRITE_TAC[];
      ALL_TAC]) eta_4x_87_cs0 THEN
  FULL_INIT_TAC THEN
  ARM_STEPS_TAC ETA_4X_87_EXEC (1--9) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC ETA_4X_87_ZERO_RULES THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let ETA_4X_87_LOOP_INIT_TAC =
  FULL_INIT_TAC THEN
  ARM_STEPS_TAC ETA_4X_87_EXEC (1--9) THEN
  ETA_4X_87_TEST_TAC eta_4x_87_cs0 THEN
  SUBGOAL_THEN (mk_neg(rhs(concl(REWRITE_CONV ETA_4X_87_ZERO_RULES
                                  (ETA_4X_87_DONE `0`)))))
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ETA_4X_87_MINIMALITY_TAC `0` THEN
    REWRITE_TAC ETA_4X_87_ZERO_RULES THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `~(k0 = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  ARM_STEPS_TAC ETA_4X_87_EXEC (10--10) THEN
  ETA_4X_87_ARGS_32_TAC (last eta_4x_87_cs0) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC ETA_4X_87_ZERO_RULES THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* The loop body, for iteration i, with the counts before it as c0, ..., c3  *)
(* (their definitions packed into one conjunction, and put back before the   *)
(* events are matched with the template). The call of mld_rej_eta_c87 for    *)
(* polynomial m on the block of the bytes from t = 136 + 136 * i on gets its *)
(* count c, declassifies the part of D from 2 * t on that it reads, and adds *)
(* the coefficients of the block after the count, giving those of the bytes  *)
(* up to t + 136.                                                            *)
(* ------------------------------------------------------------------------- *)

let ETA_4X_87_IS_ABBREV tm =
  match tm with
    Comb(Comb(Const("=",_),Comb(Comb(Const("MIN",_),_),_)),Var(n,_)) ->
      String.length n = 2 && String.sub n 0 1 = "c"
  | _ -> false;;

let ETA_4X_87_ABBREV_TAC =
  MAP_EVERY (fun m ->
    let t = eta_4x_87_count (el m ETA_4X_87_DS) `i:num` in
    ASSUME_TAC(SPECL [`256`; rand t] (ARITH_RULE `!a b. MIN a b <= a`)) THEN
    ABBREV_TAC(mk_eq(mk_var("c"^string_of_int m,`:num`),t))) (0--3) THEN
  (fun (asl,w) ->
    let hs,ks = partition (fun (_,th) -> ETA_4X_87_IS_ABBREV(concl th))
                          asl in
    let cth = end_itlist CONJ (map snd hs) in
    (null_meta,[("",ASSUME(concl cth))::ks,w],
     fun i ths -> PROVE_HYP (INSTANTIATE_ALL i cth) (hd ths)));;

let ETA_4X_87_ABBREV m =
  let eq = mk_eq(eta_4x_87_count (el m ETA_4X_87_DS) `i:num`,
                 mk_var("c"^string_of_int m,`:num`)) in
  fun (asl,w) ->
    tryfind (fun (_,th) -> find (fun th' -> concl th' = eq) (CONJUNCTS th))
            asl;;

let ETA_4X_87_UNABBREV_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_conj(concl th) && ETA_4X_87_IS_ABBREV(lhand(concl th))
    then MAP_EVERY (SUBST_ALL_TAC o SYM) (CONJUNCTS th) else NO_TAC);;

let ETA_4X_87_COMBINE_TAC m n =
  let h = el m ETA_4X_87_NONCES and d = el m ETA_4X_87_DS
  and vec = el m ETA_4X_87_VECS in
  let c = mk_var("c"^string_of_int m,`:num`)
  and s = mk_var("s"^string_of_int n,`:armstate`) in
  let strm = eta_4x_87_stream h in
  let goal = vsubst [vec,`vec:int64`; strm,`str:num->byte`; s,`s:armstate`;
                     d,`D:bool list`]
   `!k. k < MIN 256 (LENGTH(FILTER (\x:bool. x)
                    (SUB_LIST(0,2 * (136 + 136 * (i + 1))) D)))
        ==> read (memory :> bytes32(word_add vec (word(4 * k)))) s =
            EL k (mld_rej_eta_list 2 str (2 * (136 + 136 * (i + 1))))` in
  let isvecfact pat th =
    is_forall(concl th) && free_in vec (concl th) && free_in s (concl th) &&
    can (term_match [] pat) (concl th) in
  W(fun gl ->
    let ath = ETA_4X_87_ABBREV m gl and cnv = ETA_4X_87_CNV m gl in
    let tth = snd(find (fun (_,th) ->
                concl th = mk_comb(`mld_rej_eta_terminates 2`,strm)) (fst gl))
    and dath = snd(find (fun (_,th) ->
                concl th = mk_eq(eta_4x_87_declass h,d)) (fst gl)) in
    let sc = TRANS (SYM(SPEC `2 * (136 + 136 * i)` cnv)) ath in
    let cth = REWRITE_RULE[ARITH_RULE
                `(136 + 136 * i) + 136 = 136 + 136 * (i + 1)`;
                GSYM(SPEC `2 * (136 + 136 * (i + 1))` cnv)]
               (SPEC `136` (MATCH_MP (SPEC `2` MLD_REJ_ETA_CTR_BLOCK) sc))
    and dth = REWRITE_RULE[dath]
               (SPEC `136` (MATCH_MP
                 (SPEC `2` MLD_POLY_UNIFORM_ETA_DECLASS_BLOCK)
                 (CONJ tth sc))) in
    RULE_ASSUM_TAC(REWRITE_RULE[cth; dth]) THEN
    SUBGOAL_THEN goal ASSUME_TAC THENL
     [X_GEN_TAC `k:num` THEN
      REWRITE_TAC[cnv] THEN DISCH_TAC THEN
      MP_TAC(SPECL [`2`; strm; `136 + 136 * i`; c; `136`; `k:num`]
                   MLD_REJ_ETA_EL_BLOCK) THEN
      REWRITE_TAC[ARITH_RULE `(136 + 136 * i) + 136 = 136 + 136 * (i + 1)`]
      THEN ANTS_TAC THENL [ASM_REWRITE_TAC[sc]; DISCH_THEN SUBST1_TAC] THEN
      COND_CASES_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check
          (isvecfact `!k. k < c ==> P k`)) THEN
        ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o check
          (isvecfact `!k. c <= k /\ k < d ==> P k`)) THEN
        ASM_REWRITE_TAC[GSYM NOT_LT; cnv]];
      ALL_TAC]);;

let ETA_4X_87_CALL1_TAC m n =
  let h = el m ETA_4X_87_NONCES in
  let c = mk_var("c"^string_of_int m,`:num`) in
  let b = mk_abs(`j:num`,
           mk_comb(eta_4x_87_stream h,`(136 + 136 * i) + j`)) in
  ETA_4X_87_ARGS_32_TAC c THEN
  ETA_4X_87_CALL_TAC "H_REJ"
   [`read X0 s`; c; `read X2 s`; b; `pc:num`; `read X30 s`] n THEN
  ETA_4X_87_COMBINE_TAC m n;;

let ETA_4X_87_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  ETA_4X_87_ABBREV_TAC THEN
  FULL_INIT_TAC THEN

  (*** Squeezing one more block from each state ***)

  ARM_STEPS_TAC ETA_4X_87_EXEC (1--7) THEN
  MAP_EVERY (fun m -> KECCAK_STATE_AT_TAC (ETA_4X_87_ST m)) (0--3) THEN
  ETA_4X_87_CALL_TAC "H_SQUEEZE"
   ([`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `1`;
     `read X5 s`] @
    map (fun sv -> mk_comb(`keccak_squeeze (1 + i)`,sv)) ETA_4X_87_SVS @
    [`pc:num`; `read SP s`; `read X30 s`]) 8 THEN
  ETA_4X_87_BLOCKS_TAC THEN

  (*** Sampling from each block after the coefficients so far ***)

  MAP_EVERY (fun (m,k) ->
    ARM_STEPS_TAC ETA_4X_87_EXEC (k--(12 + 6 * m)) THEN
    ETA_4X_87_CALL1_TAC m (13 + 6 * m)) [0,9; 1,14; 2,20; 3,26] THEN

  (*** The test of whether all four have 256 coefficients now ***)

  MAP_EVERY ETA_4X_87_ARGS_32_TAC (butlast eta_4x_87_cs1) THEN
  ARM_STEPS_TAC ETA_4X_87_EXEC (32--40) THEN
  ETA_4X_87_TEST_TAC eta_4x_87_cs1 THEN ETA_4X_87_LS_TAC THEN
  ETA_4X_87_ARGS_32_TAC (last eta_4x_87_cs1) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  ETA_4X_87_UNABBREV_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The exit of the loop, where all four have 256 coefficients ***)

let ETA_4X_87_EXIT_TAC =
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  MAP_EVERY (fun d ->
    SUBGOAL_THEN (mk_eq(eta_4x_87_count d `k0:num`,`256`))
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC]) ETA_4X_87_DS THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let ETA_4X_87_LOOP_TAC =
  REWRITE_TAC[EQF_INTRO(ASSUME `~(k0 = 0)`)] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `k0:num`
   `pc + mldsa87_poly_uniform_eta_4x_loop1`
   `pc + mldsa87_poly_uniform_eta_4x_loop1_exit` ETA_4X_87_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ETA_4X_87_LOOP_INIT_TAC;
    ETA_4X_87_BODY_TAC;
    ETA_4X_87_EXIT_TAC];;

(* ------------------------------------------------------------------------- *)
(* Releasing the state, zeroing the buffers and the extended seeds, the      *)
(* stack guard and the return, with the polynomials as mld_poly_uniform_eta. *)
(* ------------------------------------------------------------------------- *)

let ETA_4X_87_RESULTS_TAC =
  MAP_EVERY (fun (h,(d,vec)) ->
    SUBGOAL_THEN
     (vsubst [h,`h:byte`; vec,`vec:int64`]
       `!k. k < 256
            ==> read (memory :> bytes32(word_add vec (word(4 * k)))) s0 =
                mld_poly_uniform_eta 2 sd h k`)
     ASSUME_TAC THENL
     [MATCH_MP_TAC ETA_4X_87_RESULT THEN
      MAP_EVERY EXISTS_TAC [d; `k0:num`] THEN ASM_REWRITE_TAC[];
      ALL_TAC])
   (zip ETA_4X_87_NONCES (zip ETA_4X_87_DS ETA_4X_87_VECS));;

let ETA_4X_87_PART3_TAC =
  FULL_INIT_TAC THEN ETA_4X_87_RESULTS_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `k0:num`)) THEN
  ETA_4X_87_GOT_TAC THEN
  ARM_STEPS_TAC ETA_4X_87_EXEC (1--2) THEN
  ETA_4X_87_CALL_TAC "H_RELEASE"
   [`read X0 s`; `pc:num`; `read SP s`; `read X30 s`] 3 THEN
  ARM_STEPS_TAC ETA_4X_87_EXEC (4--7) THEN
  LIBC_PLT_TAC ETA_4X_87_EXEC 7 THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" ETA_4X_87_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref ETA_4X_87_ALLOWED) 12 THEN
  ARM_STEPS_TAC ETA_4X_87_EXEC (13--17) THEN
  LIBC_PLT_TAC ETA_4X_87_EXEC 17 THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" ETA_4X_87_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref ETA_4X_87_ALLOWED) 22 THEN
  ARM_STEPS_TAC ETA_4X_87_EXEC (23--23) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC ETA_4X_87_EXEC (24--37) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together.                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  ETA_4X_87_INTRO_TAC THEN ETA_4X_87_SETUP_TAC THEN
  ETA_4X_87_DECLASS_TAC THEN ETA_4X_87_STATES_TAC THEN
  ETA_4X_87_MINIMAL_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa87_poly_uniform_eta_4x_loop1_exit`
   ETA_4X_87_A2 THEN CONJ_TAC THENL
   [ENSURES_EVENTS_SEQUENCE_TAC
     `pc + mldsa87_poly_uniform_eta_4x_after_mld_rej_eta_c87_4`
     ETA_4X_87_A1 THEN CONJ_TAC THENL
     [ETA_4X_87_PART1_TAC;
      ASM_CASES_TAC `k0 = 0` THENL
       [ETA_4X_87_NOLOOP_TAC; ETA_4X_87_LOOP_TAC]];
    ETA_4X_87_PART3_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;
