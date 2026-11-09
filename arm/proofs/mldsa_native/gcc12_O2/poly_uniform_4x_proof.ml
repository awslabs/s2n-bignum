(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform sampling of four polynomials mod q from four seeds: the proof     *)
(* (see poly_uniform_4x_spec.ml). It follows the proof for                   *)
(* mlkem_poly_rej_uniform_x4 of mlkem-native, with the FULL theorems of the  *)
(* callees, whose results and events the proof combines at each call.        *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/poly_uniform_4x_spec.ml";;
needs "arm/proofs/utils/mldsa_native_sampling.ml";;

let POLY_UNIFORM_4X_EXEC = MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The seeds, polynomials and absorbed states, and the terms for the number  *)
(* of coefficients of each after t blocks after the first five: the count    *)
(* MIN 256 (LENGTH(mld_rej_uniform_list s (280 + 56 * t))) for the stream s  *)
(* of the seed.                                                              *)
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

let poly_uniform_4x_count0 m =
  rhs(concl(REWRITE_CONV[MULT_CLAUSES; ADD_CLAUSES]
             (poly_uniform_4x_count m `0`)));;

let poly_uniform_4x_cs0 = map poly_uniform_4x_count0 POLY_UNIFORM_4X_MS
and poly_uniform_4x_cs1 =
  map (fun m -> poly_uniform_4x_count m `i + 1`) POLY_UNIFORM_4X_MS;;

let POLY_UNIFORM_4X_DONE n =
  list_mk_conj
   (map (fun m -> mk_binop `(<=):num->num->bool` `256`
                   (mk_comb(`LENGTH:(int32)list->num`,
                     poly_uniform_4x_list m (poly_uniform_4x_groups n))))
        POLY_UNIFORM_4X_MS);;

(* ------------------------------------------------------------------------- *)
(* The events, as for mlkem_poly_rej_uniform_x4: those to the end of the     *)
(* four first samplings (p1), of the loop over the k0 more blocks that are   *)
(* needed, k0 being the least number with which all four have 256            *)
(* coefficients, or of the branch round it if k0 = 0, and those of releasing *)
(* the state, zeroing the buffers and returning (p3).                        *)
(* ------------------------------------------------------------------------- *)

let POLY_UNIFORM_4X_TEMPLATE =
  let args = [`vec0:int64`; `vec1:int64`; `vec2:int64`; `vec3:int64`;
              `seed:int64`; `M0:num`; `M1:num`; `M2:num`; `M3:num`;
              `guard:int64`; `mf:int64`; `pc:num`; `stackpointer:int64`;
              `returnaddress:int64`] in
  let fty = itlist (fun a t -> mk_fun_ty (type_of a) t) args
                   `:(uarch_event)list` in
  let fv n = mk_var(n,fty) in
  let app n = list_mk_comb(fv n,args) in
  let k0 = mk_comb(`(minimal):(num->bool)->num`,
                   mk_abs(`n:num`,POLY_UNIFORM_4X_DONE `n:num`)) in
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

let POLY_UNIFORM_4X_ALLOWED =
  [`pc:num`; `vec0:int64`; `vec1:int64`; `vec2:int64`; `vec3:int64`;
   `seed:int64`; `M0:num`; `M1:num`; `M2:num`; `M3:num`; `guard:int64`;
   `mf:int64`; `stackpointer:int64`; `returnaddress:int64`; `i:num`;
   `c0:num`; `c1:num`; `c2:num`; `c3:num`;
   `f_ev_loop:int64->int64->int64->int64->int64->num->num->num->num->
              int64->int64->num->int64->int64->num->(uarch_event)list`];;

let POLY_UNIFORM_4X_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc POLY_UNIFORM_4X_EXEC name
    ilist POLY_UNIFORM_4X_ALLOWED n;;

(* ------------------------------------------------------------------------- *)
(* The four buffers of 864 bytes for five blocks each are aligned to 32      *)
(* bytes within the stack frame, so that their addresses depend on whether   *)
(* the stack pointer is a multiple of 32 or just of 16; the four states      *)
(* follow them, at a fixed offset.                                           *)
(* ------------------------------------------------------------------------- *)

let POLY_UNIFORM_4X_BUFFER_ADDRESS = prove
 (`!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 463)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 448 else 432))`,
  SUBGOAL_THEN
   `(!x:int64. aligned 16 x <=> word_and x (word 15) = word 0) /\
    (!x:int64. aligned 32 x <=> word_and x (word 31) = word 0)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [CONJ_TAC THEN GEN_TAC THEN REWRITE_TAC[aligned; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[] THENL
     [MP_TAC(ISPECL [`x:int64`; `4`] (CONJUNCT1 WORD_AND_MASK_WORD));
      MP_TAC(ISPECL [`x:int64`; `5`] (CONJUNCT1 WORD_AND_MASK_WORD))] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[DIVIDES_MOD; GSYM VAL_EQ_0; VAL_WORD; DIMINDEX_64] THEN
    SIMP_TAC[MOD_LT; ARITH_RULE `x MOD 16 < 16`; ARITH_RULE `x MOD 32 < 32`;
             ARITH_RULE `x < 16 ==> x < 2 EXP 64`;
             ARITH_RULE `x < 32 ==> x < 2 EXP 64`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[MOD_LT; ARITH_RULE `x MOD 16 < 16 ==> x MOD 16 < 2 EXP 64`;
             MOD_LT_EQ; ARITH_EQ; ARITH_RULE `x MOD 32 < 32`;
             ARITH_RULE `x MOD 16 < 18446744073709551616`;
             ARITH_RULE `x MOD 32 < 18446744073709551616`];
    GEN_TAC THEN COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
    W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w))]);;

let POLY_UNIFORM_4X_BUFFER_TAC =
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 463))
             (word 18446744073709551584):int64 =
    word_add stackpointer (word(if aligned 32 stackpointer then 448 else 432))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC POLY_UNIFORM_4X_BUFFER_ADDRESS THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

let POLY_UNIFORM_4X_NORMALIZE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th
    else th);;

let POLY_UNIFORM_4X_ST m =
  mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
          mk_comb(`word:num->int64`,mk_small_numeral(3912 + 200 * m)));;

(*** The GOT entries in the form in the preconditions of the callees ***)

let POLY_UNIFORM_4X_GOT_TAC =
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
(* the coefficients so far and its state. At the exit of the loop the        *)
(* polynomials are complete.                                                 *)
(* ------------------------------------------------------------------------- *)

let POLY_UNIFORM_4X_FRAME =
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
  read (memory :> bytes64 (word_add stackpointer (word 400))) s = vec0 /\
  read (memory :> bytes64 (word_add stackpointer (word 408))) s = vec1 /\
  read (memory :> bytes64 (word_add stackpointer (word 416))) s = vec2 /\
  read (memory :> bytes64 (word_add stackpointer (word 424))) s = vec3 /\
  read (memory :> bytes64 (word_add stackpointer (word 4712))) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard))) s =
  guard /\
  read (memory :> bytes64 guard) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word got_memset))) s = mf /\
  read (memory :> bytes(ea,el)) s = ev /\
  read X22 s =
  word_add stackpointer (word(if aligned 32 stackpointer then 448 else 432)) /\
  read X25 s =
  word_add stackpointer
   (word((if aligned 32 stackpointer then 448 else 432) + 864)) /\
  read X24 s =
  word_add stackpointer
   (word((if aligned 32 stackpointer then 448 else 432) + 1728)) /\
  read X23 s =
  word_add stackpointer
   (word((if aligned 32 stackpointer then 448 else 432) + 2592)) /\
  read X26 s = word_add stackpointer (word 3912)`;;

let POLY_UNIFORM_4X_POLY =
 `read (R:(armstate,int64)component) s =
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
           (vsubst [r,`R:(armstate,int64)component`; vec,`vec:int64`;
                    m,`M:num`; st,`st:int64`; sv,`S:1600 word`]
                   POLY_UNIFORM_4X_POLY))
        (zip regs (zip POLY_UNIFORM_4X_VECS (zip POLY_UNIFORM_4X_MS
           (zip (map POLY_UNIFORM_4X_ST (0--3)) POLY_UNIFORM_4X_SVS)))));;

let POLY_UNIFORM_4X_A1 =
  let t = vsubst [`0`,`i:num`]
           (list_mk_conj(POLY_UNIFORM_4X_POLYS [`X19`; `X20`; `X21`; `X0`])) in
  let t' = rhs(concl(REWRITE_CONV[MULT_CLAUSES; ADD_CLAUSES] t)) in
  mk_abs(`s:armstate`,
         list_mk_conj(conjuncts t' @ conjuncts POLY_UNIFORM_4X_FRAME));;

let POLY_UNIFORM_4X_INV =
  list_mk_abs([`i:num`; `s:armstate`],
    list_mk_conj(POLY_UNIFORM_4X_POLYS [`X19`; `X20`; `X21`; `X28`] @
                 [`read X27 s = word 255`] @
                 conjuncts POLY_UNIFORM_4X_FRAME));;

let POLY_UNIFORM_4X_A2 =
  let res m vec =
    vsubst [m,`M:num`; vec,`vec:int64`]
     `!k. k < 256
          ==> read (memory :> bytes32(word_add vec (word(4 * k)))) s =
              EL k (mld_rej_uniform_list (mld_shake128_stream 34 M)
                                         (280 + 56 * k0))` in
  mk_abs(`s:armstate`,
    list_mk_conj(map2 res POLY_UNIFORM_4X_MS POLY_UNIFORM_4X_VECS @
                 conjuncts POLY_UNIFORM_4X_FRAME));;

(*** The result for one polynomial from the first 280 + 56 * k0 groups ***)

let POLY_UNIFORM_4X_RESULT = prove
 (`!vec:int64 M k0 (s:armstate).
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
(* The setup: the callee theorems, the template, the stack frame and the     *)
(* saved registers, the stack guard as canary, the absorbed states S0, ...,  *)
(* S3, with the streams as their bytes, and k0 with its minimality.          *)
(* ------------------------------------------------------------------------- *)

let POLY_UNIFORM_4X_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLDSA_NATIVE_SHAKE128X4_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_FULL
               th) "H_RELEASE" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP
       MLDSA_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_FULL th)
     "H_ABSORB") THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] th)
     "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE128X4_INIT_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_INIT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_SQUEEZE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_REJ_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_REJ" THEN
  CONCRETIZE_F_EVENTS_TAC POLY_UNIFORM_4X_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst POLY_UNIFORM_4X_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

let POLY_UNIFORM_4X_SETUP_TAC =
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 4720):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `432 <= (if aligned 32 (stackpointer:int64) then 448 else 432) /\
    (if aligned 32 (stackpointer:int64) then 448 else 432) <= 448`
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
(* Counts as 32-bit arguments, the states after absorbing, and the blocks    *)
(* after squeezing as bytes of the streams (their addresses normalized as in *)
(* the precondition of mld_rej_uniform_c), the states after them as bytes.   *)
(* ------------------------------------------------------------------------- *)

let POLY_UNIFORM_4X_ARGS_32_TAC c =
  MP_TAC(SPEC c WORD_ZX_32_SMALL) THEN
  ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN
    (ARITH_TAC ORELSE
     FIRST_ASSUM(fun th ->
      if (is_binary "<" (concl th) || is_binary "<=" (concl th)) &&
         lhand(concl th) = c
      then MP_TAC th THEN ARITH_TAC else NO_TAC));
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))];;

let POLY_UNIFORM_4X_ABSORBED_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM MLD_KECCAK_ABSORB_ONCE]) THEN
  W(fun (asl,w) ->
    let abs = filter (fun th -> can (term_match []
                `mld_keccak_absorb_once r p n m = (S:1600 word)`) (concl th))
               (map snd asl) in
    RULE_ASSUM_TAC(fun th ->
      if can (term_match [] `read (memory :> wbytes a) s = (x:1600 word)`)
             (concl th)
      then REWRITE_RULE abs th else th));;

let POLY_UNIFORM_4X_SHIFT168 =
  REWRITE_RULE[ARITH_RULE `0 < 168`]
   (SPEC `168` MLD_KECCAK_SQUEEZE_BYTE_SHIFT);;

let POLY_UNIFORM_4X_BLOCKS_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
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
  POLY_UNIFORM_4X_NORMALIZE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The four first samplings, from the bytes of the first five blocks.        *)
(* ------------------------------------------------------------------------- *)

let POLY_UNIFORM_4X_CALL0_TAC m n =
  POLY_UNIFORM_4X_CALL_TAC "H_REJ"
   [`read X0 s`; `0`; `read X2 s`; `840`;
    poly_uniform_4x_stream (el m POLY_UNIFORM_4X_MS); `pc:num`;
    `read X30 s`] n THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_REJ_UNIFORM_CTR_FIRST; LE_0; SUB_0;
                              ARITH_RULE `840 DIV 3 = 280`]);;

let POLY_UNIFORM_4X_PART1_TAC =
  FULL_INIT_TAC THEN
  ARM_STEPS_TAC POLY_UNIFORM_4X_EXEC (1--3) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC POLY_UNIFORM_4X_EXEC (4--12) THEN
  POLY_UNIFORM_4X_BUFFER_TAC THEN
  ARM_STEPS_TAC POLY_UNIFORM_4X_EXEC (13--28) THEN
  POLY_UNIFORM_4X_NORMALIZE_TAC THEN
  POLY_UNIFORM_4X_CALL_TAC "H_INIT" [`read X0 s`; `pc:num`; `read X30 s`] 29
  THEN
  ARM_STEPS_TAC POLY_UNIFORM_4X_EXEC (30--36) THEN POLY_UNIFORM_4X_GOT_TAC THEN
  POLY_UNIFORM_4X_CALL_TAC "H_ABSORB"
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`; `34`;
    `M0:num`; `M1:num`; `M2:num`; `M3:num`; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] 37 THEN
  POLY_UNIFORM_4X_ABSORBED_TAC THEN
  ARM_STEPS_TAC POLY_UNIFORM_4X_EXEC (38--44) THEN
  POLY_UNIFORM_4X_CALL_TAC "H_SQUEEZE"
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `5`; `read X5 s`;
    `S0:1600 word`; `S1:1600 word`; `S2:1600 word`; `S3:1600 word`;
    `pc:num`; `read SP s`; `read X30 s`] 45 THEN
  POLY_UNIFORM_4X_BLOCKS_TAC THEN
  MAP_EVERY (fun m ->
    ARM_STEPS_TAC POLY_UNIFORM_4X_EXEC ((46 + 6 * m)--(50 + 6 * m)) THEN
    POLY_UNIFORM_4X_CALL0_TAC m (51 + 6 * m)) (0--3) THEN
  MAP_EVERY POLY_UNIFORM_4X_ARGS_32_TAC (butlast poly_uniform_4x_cs0) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* The loop test, as for mlkem_poly_rej_uniform_x4: the code compares the    *)
(* four counts with 255 as 32-bit words, combining the tests with CCMP, and  *)
(* goes on unless all four are 256; whether all four are 256 after block     *)
(* i + 1 is whether i + 1 = k0, by the minimality of k0.                     *)
(* ------------------------------------------------------------------------- *)

let POLY_UNIFORM_4X_CMP = prove
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

let POLY_UNIFORM_4X_TEST_PROVE_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `n0 < 2 EXP 32 /\ n1 < 2 EXP 32 /\ n2 < 2 EXP 32 /\ n3 < 2 EXP 32`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[POLY_UNIFORM_4X_CMP] THEN
  REWRITE_TAC[TAUT `(if a then b else F) <=> a /\ b`;
              ARITH_RULE `255 <= n /\ ~(n = 255) <=> 255 < n`] THEN
  REPEAT COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV THEN ASM_ARITH_TAC;;

let POLY_UNIFORM_4X_TEST_TAC cs =
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
                        POLY_UNIFORM_4X_TEST_PROVE_TAC) in
        ASSUME_TAC(REWRITE_RULE[MP (SPECL cs lth) bth;
                                ARITH_RULE `255 < MIN 256 x <=> 256 <= x`] th)
    | _ -> NO_TAC);;

let POLY_UNIFORM_4X_LS_TAC =
  SUBGOAL_THEN (mk_eq(POLY_UNIFORM_4X_DONE `i + 1`,`~(i + 1 < k0)`))
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [EQ_TAC THENL
     [DISCH_THEN(fun dth -> DISCH_THEN(fun lth ->
        POLY_UNIFORM_4X_MINIMALITY_TAC `i + 1` THEN REWRITE_TAC[dth; lth]));
      DISCH_TAC THEN SUBGOAL_THEN `i + 1 = k0` SUBST1_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`i < k0`; `~(i + 1 < k0)`] THEN ARITH_TAC;
        REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The branch round the loop when no more blocks are needed, and the entry   *)
(* to the loop otherwise.                                                    *)
(* ------------------------------------------------------------------------- *)

let POLY_UNIFORM_4X_NOLOOP_TAC =
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES; ADD_CLAUSES]) THEN
  REWRITE_TAC[] THEN
  MAP_EVERY (fun c ->
    SUBGOAL_THEN (mk_eq(c,`256`))
     (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[ARITH_RULE `MIN a b = a <=> a <= b`] THEN ASM_REWRITE_TAC[];
      ALL_TAC]) poly_uniform_4x_cs0 THEN
  FULL_INIT_TAC THEN
  ARM_STEPS_TAC POLY_UNIFORM_4X_EXEC (1--10) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let POLY_UNIFORM_4X_LOOP_INIT_TAC =
  FULL_INIT_TAC THEN
  ARM_STEPS_TAC POLY_UNIFORM_4X_EXEC (1--10) THEN
  POLY_UNIFORM_4X_TEST_TAC poly_uniform_4x_cs0 THEN
  SUBGOAL_THEN (mk_neg(rhs(concl(REWRITE_CONV[MULT_CLAUSES; ADD_CLAUSES]
                                  (POLY_UNIFORM_4X_DONE `0`)))))
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [POLY_UNIFORM_4X_MINIMALITY_TAC `0` THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `~(k0 = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  ARM_STEPS_TAC POLY_UNIFORM_4X_EXEC (11--11) THEN
  POLY_UNIFORM_4X_ARGS_32_TAC (last poly_uniform_4x_cs0) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* The loop body, for iteration i. The counts before it are c0, ..., c3,     *)
(* their definitions packed into one conjunction, which keeps them from the  *)
(* arithmetic of NONOVERLAPPING_TAC, and put back before the events are      *)
(* matched with the template. After squeezing one more block of each, each   *)
(* call of mld_rej_uniform_c adds the accepted values of its 56 groups after *)
(* the count, giving those of the first 280 + 56 * (i + 1) groups.           *)
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
  and s = mk_var("s"^string_of_int n,`:armstate`) in
  let strm = poly_uniform_4x_stream mv in
  let goal = vsubst [vec,`vec:int64`; strm,`str:num->byte`; s,`s:armstate`]
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
  POLY_UNIFORM_4X_ARGS_32_TAC c THEN
  POLY_UNIFORM_4X_CALL_TAC "H_REJ"
   [`read X0 s`; c; `read X2 s`; `168`; b; `pc:num`; `read X30 s`] n THEN
  POLY_UNIFORM_4X_COMBINE_TAC m n;;

let POLY_UNIFORM_4X_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  POLY_UNIFORM_4X_ABBREV_TAC THEN
  FULL_INIT_TAC THEN

  (*** Squeezing one more block from each state ***)

  ARM_STEPS_TAC POLY_UNIFORM_4X_EXEC (1--7) THEN
  MAP_EVERY (fun m -> KECCAK_STATE_AT_TAC (POLY_UNIFORM_4X_ST m)) (0--3) THEN
  POLY_UNIFORM_4X_CALL_TAC "H_SQUEEZE"
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `1`; `read X5 s`;
    `keccak_squeeze (5 + i) (S0:1600 word)`;
    `keccak_squeeze (5 + i) (S1:1600 word)`;
    `keccak_squeeze (5 + i) (S2:1600 word)`;
    `keccak_squeeze (5 + i) (S3:1600 word)`;
    `pc:num`; `read SP s`; `read X30 s`] 8 THEN
  POLY_UNIFORM_4X_BLOCKS_TAC THEN

  (*** Sampling from each block after the coefficients so far ***)

  MAP_EVERY (fun m ->
    ARM_STEPS_TAC POLY_UNIFORM_4X_EXEC ((9 + 6 * m)--(13 + 6 * m)) THEN
    POLY_UNIFORM_4X_CALL1_TAC m (14 + 6 * m)) (0--3) THEN

  (*** The test of whether all four have 256 coefficients now ***)

  MAP_EVERY POLY_UNIFORM_4X_ARGS_32_TAC (butlast poly_uniform_4x_cs1) THEN
  ARM_STEPS_TAC POLY_UNIFORM_4X_EXEC (33--41) THEN
  POLY_UNIFORM_4X_TEST_TAC poly_uniform_4x_cs1 THEN POLY_UNIFORM_4X_LS_TAC THEN
  POLY_UNIFORM_4X_ARGS_32_TAC (last poly_uniform_4x_cs1) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  POLY_UNIFORM_4X_UNABBREV_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

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
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let POLY_UNIFORM_4X_LOOP_TAC =
  REWRITE_TAC[EQF_INTRO(ASSUME `~(k0 = 0)`)] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `k0:num` `pc + mldsa_poly_uniform_4x_loop1`
   `pc + mldsa_poly_uniform_4x_loop1_exit` POLY_UNIFORM_4X_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    POLY_UNIFORM_4X_LOOP_INIT_TAC;
    POLY_UNIFORM_4X_BODY_TAC;
    POLY_UNIFORM_4X_EXIT_TAC];;

(* ------------------------------------------------------------------------- *)
(* Releasing the state, zeroing the buffers, the stack guard and the return, *)
(* with the polynomials as mld_poly_uniform of the seeds.                    *)
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
  POLY_UNIFORM_4X_GOT_TAC THEN
  ARM_STEPS_TAC POLY_UNIFORM_4X_EXEC (1--2) THEN
  POLY_UNIFORM_4X_CALL_TAC "H_RELEASE"
   [`read X0 s`; `pc:num`; `read SP s`; `read X30 s`] 3 THEN
  ARM_STEPS_TAC POLY_UNIFORM_4X_EXEC (4--7) THEN
  LIBC_PLT_TAC POLY_UNIFORM_4X_EXEC 7 THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" POLY_UNIFORM_4X_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref POLY_UNIFORM_4X_ALLOWED) 12 THEN
  ARM_STEPS_TAC POLY_UNIFORM_4X_EXEC (13--13) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC POLY_UNIFORM_4X_EXEC (14--28) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together.                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  POLY_UNIFORM_4X_INTRO_TAC THEN POLY_UNIFORM_4X_SETUP_TAC THEN
  POLY_UNIFORM_4X_STATES_TAC THEN POLY_UNIFORM_4X_MINIMAL_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mldsa_poly_uniform_4x_loop1_exit`
   POLY_UNIFORM_4X_A2 THEN CONJ_TAC THENL
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
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;
