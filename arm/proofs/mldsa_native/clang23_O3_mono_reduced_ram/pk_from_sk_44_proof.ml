(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The public key of a secret key: the proof (see pk_from_sk_44_spec.ml).   *)
(* clang has inlined the checks of s2, the comparison of t0 and the hash of  *)
(* the public key into the function, which the proof composes with the       *)
(* theorems for its callees and for those parts (inline_pk_from_sk_44.ml),   *)
(* in the order of the code, from the prologue (with the probe of the stack  *)
(* and the buffers 32-byte aligned at stackpointer + b, b = 5344 or 5328     *)
(* by the alignment of the stack pointer) to the return.                     *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/pk_from_sk_44_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyeta_unpack_44_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_ntt_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/lazy_eq_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_probe.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_pk_from_sk_44.ml";;
needs "arm/proofs/utils/mldsa_native_verify.ml";;
needs "arm/proofs/utils/mldsa_native_top.ml";;
needs "arm/proofs/utils/mldsa_native_wrap.ml";;

let PK44_EXEC = MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;
let PK44_MC = mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc;;

let PK44_ALLOWED =
  [`pk:int64`; `sk:int64`; `skb:num->byte`; `guard:int64`; `mf:int64`;
   `mc:int64`; `pc:num`; `stackpointer:int64`; `returnaddress:int64`;
   `r:num`];;

let PK44_ARGS = "pk sk r valid guard mf mc pc stackpointer returnaddress";;

let PK44_LAMBDA =
  "\\(pk:int64) (sk:int64) (r:num) (valid:bool) (guard:int64) (mf:int64) " ^
  "(mc:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).";;

let PK44_TEMPLATE =
  let f n = "(f_ev_" ^ n ^ " " ^ PK44_ARGS ^ ")" in
  parse_term(PK44_LAMBDA ^ " if aligned 32 stackpointer " ^
    "then (if valid then " ^ f "av" ^ " else " ^ f "ai" ^ ") " ^
    "else (if valid then " ^ f "uv" ^ " else " ^ f "ui" ^ ") " ^
    ":(uarch_event)list");;

let PK44_VALID = `mld_pk_from_sk_valid 4 4 2 mld_polyeta_unpack_2 96 skb`;;

let PK44_CPT =
  MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL;;

let PK44_CALLEES_TAC =
  FIRST_ASSUM(fun th ->
    let m1 = CONJUNCT1 th in
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] m1)
     "H_MEMSET" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP PK44_CPT th) "H_CPT") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYETA_UNPACK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
   "H_UNPACK" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYVECL_CHKNORM_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
   "H_CHKL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
   "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC KG_MEMCMP44 "H_CMP" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC KG_SHAKE44 "H_SHAKE" THEN
  MAP_EVERY (fun (th,k) ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC th ("H_L"^string_of_int k))
   (zip PK44_CHK_THS (2--5));;

let PK44_SETUP_TAC =
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst PK44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 12672):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
    SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
    SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    let r = "X"^string_of_int n in
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (mk_const(r,[]))) (19--29) THEN
  ABBREV_TAC `r = mld_sk_rho skb`;;

(*** The chunks of 16 and 32 bytes of the first 128 bytes of sk ***)
let PK44_SK_CHUNKS_TAC =
  W(fun (asl,w) ->
    let skf = find (fun th -> can (term_match []
       `!j. j < 2560 ==> read(memory :> bytes8(word_add sk (word j))) s = skb j`) (concl th)) (map snd asl) in
    MAP_EVERY (fun m ->
      let th = MP (SPECL [`sk:int64`; `2560`; `skb:num->byte`;
                          rand(lhand(rand(snd(dest_forall(concl skf)))));
                          mk_small_numeral m] BYTES128_OF_BYTES8)
                  (CONJ skf (EQT_ELIM(NUM_REDUCE_CONV
                     (subst [mk_small_numeral m,`m:num`] `16 * m + 16 <= 2560`)))) in
      ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV THENC
                           REWRITE_CONV[WORD_ADD_0]) th)) (0--7));;

let PK44_SK256_TAC =
  W(fun (asl,_) ->
    let f128 = mapfilter (fun (_,th) ->
      let c = concl th in
      if is_eq c && can (term_match [] `read (memory :> bytes128 a) (s0:armstate)`) (lhs c)
      then th else fail()) asl in
    MAP_EVERY (fun j ->
      let base = if j = 0 then `sk:int64` else
        mk_comb(`word_add (sk:int64)`, mk_comb(`word:num->int64`, mk_small_numeral(32 * j))) in
      let tm = subst [base,`A:int64`] `read (memory :> bytes256 A) (s0:armstate)` in
      let eth = GEN_REWRITE_CONV I [el 0 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] tm in
      let eth = CONV_RULE(RAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) eth in
      ASSUME_TAC(REWRITE_RULE f128 eth)) (0--3));;

let PK44_BUF_TAC =
  FIRST_ASSUM(fun a16 ->
    if concl a16 <> `aligned 16 (stackpointer:int64)` then NO_TAC else
    let th = MP (SPEC `stackpointer:int64` (MLD_WRAP_BUFFER_RULE `5344`)) a16 in
    FIRST_ASSUM(fun cth ->
      if concl cth = `aligned 32 (stackpointer:int64)` ||
         concl cth = `~aligned 32 (stackpointer:int64)`
      then RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_RULE[cth] th])
      else NO_TAC));;

let PK44_CALL_TAC name ilist n =
  FULL_CALL_TAC PK44_MC PK44_EXEC name ilist PK44_ALLOWED n;;

let PK44_BYTES_SLICE_TAC tm =
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC];;

(*** A call of polyeta_unpack on the 96 bytes of sk at off, after state n-1 ***)
let PK44_UNPACK_CALL_TAC off n =
  let s = mk_var("s"^string_of_int(n-1),`:armstate`) in
  PK44_BYTES_SLICE_TAC (subst [mk_small_numeral off,`off:num`; s,`s:armstate`]
   `!j. j < 96 ==> read(memory :> bytes8(word_add sk (word(off + j)))) s =
                   (skb:num->byte)(off + j)`) THEN
  PK44_CALL_TAC "H_UNPACK"
   [`read X0 s`; `read X1 s`;
    subst [mk_small_numeral off,`off:num`] `\j. (skb:num->byte)(off + j)`;
    `pc:num`; `read SP s`; `read X30 s`] n;;

(*** Restate a register fact as the form of the precondition of a lemma ***)
let PK44_PATCH_TAC (patches:(term*term) list) =
  RULE_ASSUM_TAC(fun th ->
    try let c = concl th in
        let (l,r) = dest_eq c in
        let (_,nr) = find (fun (t,_) -> t = l) patches in
        let eq = prove(mk_eq(r,nr),FIRST[CONV_TAC WORD_REDUCE_CONV THEN NO_TAC; CONV_TAC WORD_RULE]) in
        TRANS th eq
    with Failure _ -> th);;

(*** A loop of the norm check of poly k of s2 ***)
let PK44_CHK_LOOP_CALL_TAC k areg accreg n =
  let sp = mk_var("s"^string_of_int(n-1),`:armstate`) in
  let rd r = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,mk_const(r,[])),sp) in
  PK44_PATCH_TAC [rd "X9", `word_zx (word_sub (word 3:int32) (word 1)):int64`;
                  rd accreg, `word_zx (word 0:int32):int64`] THEN
  PK44_CALL_TAC ("H_L"^string_of_int(k+2))
   [mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,mk_const(areg,[])),`s:armstate`);
    subst [mk_small_numeral(512 + 96 * k),`off:num`]
      `mld_polyeta_unpack_2 (\j. (skb:num->byte) (off + j))`;
    `word 3:int32`; `word 0:int32`; `pc:num`] n;;

(*** The four polynomials of s1 as slices of the vector, in the state sname ***)
let PK44_S1_SLICE_TAC s1 p sname =
  let sp = mk_var(sname,`:armstate`) in
  let off = s1 + 1024 * p in
  SUBGOAL_THEN
   (subst [mk_small_numeral off,`off:num`; mk_small_numeral p,`p:num`; sp,`s:armstate`]
     `!j. j < 256 ==> read (memory :> bytes32 (word_add stackpointer (word (off + 4 * j)))) s =
          mld_poly_of (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. (skb:num->byte) (128 + j))) p j`)
   ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[mld_poly_of] THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [] (subst [mk_small_numeral s1,`S1:num`]
           `!i. i < 1024 ==> read (memory :> bytes32 (word_add stackpointer (word (S1 + 4 * i)))) s = x i`)) (concl th)
      then MP_TAC(SPEC (subst [mk_small_numeral p,`p:num`] `256 * p + j`) th) else NO_TAC) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE (subst [mk_small_numeral s1,`S1:num`; mk_small_numeral off,`off:num`; mk_small_numeral p,`p:num`]
      `S1 + 4 * (256 * p + j) = off + 4 * j`)] THEN
    DISCH_THEN ACCEPT_TAC;
    ALL_TAC];;

(*** The NTT of poly p of s1, in place ***)
let PK44_NTT_CALL_TAC p n =
  PK44_CALL_TAC "H_NTT"
   [`read X0 s`; subst [mk_small_numeral p,`p:num`] `mld_poly_of (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. (skb:num->byte) (128 + j))) p`;
    `pc:num`; `read SP s`; `read X30 s`] n;;

let PK44_JOIN4 = prove
 (`!(sp:int64) n (b:num->byte) s.
    (!i. i < 256
         ==> read (memory :> bytes32 (word_add sp (word (n + 4 * i)))) s =
             mld_polyeta_unpack_2 (\j. b (128 + j)) i) /\
    (!i. i < 256
         ==> read (memory :> bytes32 (word_add sp (word (n + 1024 + 4 * i)))) s =
             mld_polyeta_unpack_2 (\j. b (224 + j)) i) /\
    (!i. i < 256
         ==> read (memory :> bytes32 (word_add sp (word (n + 2048 + 4 * i)))) s =
             mld_polyeta_unpack_2 (\j. b (320 + j)) i) /\
    (!i. i < 256
         ==> read (memory :> bytes32 (word_add sp (word (n + 3072 + 4 * i)))) s =
             mld_polyeta_unpack_2 (\j. b (416 + j)) i)
    ==> !i. i < 1024
            ==> read (memory :> bytes32 (word_add sp (word (n + 4 * i)))) s =
                mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. b(128 + j)) i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[mld_polyvec_unpack; mld_polyvec] THEN
  SUBGOAL_THEN `?p k. p < 4 /\ k < 256 /\ i = 256 * p + k` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC [`i DIV 256`; `i MOD 256`] THEN
    MP_TAC(SPECL [`i:num`; `256`] DIVISION) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_SIMP_TAC[DIVMOD_CHUNK] THEN
  SUBGOAL_THEN `p = 0 \/ p = 1 \/ p = 2 \/ p = 3` MP_TAC THENL
   [ASM_ARITH_TAC; DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC)] THEN
  REWRITE_TAC[ARITH_RULE `!n k. n + 4 * (256 * 0 + k) = n + 4 * k`;
              ARITH_RULE `!n k. n + 4 * (256 * 1 + k) = n + 1024 + 4 * k`;
              ARITH_RULE `!n k. n + 4 * (256 * 2 + k) = n + 2048 + 4 * k`;
              ARITH_RULE `!n k. n + 4 * (256 * 3 + k) = n + 3072 + 4 * k`;
              ARITH_RULE `!t. 128 + 96 * 0 + t = 128 + t`;
              ARITH_RULE `!t. 128 + 96 * 1 + t = 224 + t`;
              ARITH_RULE `!t. 128 + 96 * 2 + t = 320 + t`;
              ARITH_RULE `!t. 128 + 96 * 3 + t = 416 + t`] THEN
  ASM_SIMP_TAC[]);;

let PK44_S1 = `mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. (skb:num->byte)(128 + j))`;;

let PK44_JOIN4_RULE n s =
  CONV_RULE(REWRITE_CONV[ADD_ASSOC] THENC DEPTH_CONV NUM_ADD_CONV)
   (SPECL [`stackpointer:int64`; mk_small_numeral n; `skb:num->byte`; s] PK44_JOIN4);;

let PK44_NTT_JOIN4 = prove
 (`!(sp:int64) n (x:num->int32) s.
    (!i. i < 256
         ==> read (memory :> bytes32 (word_add sp (word (n + 4 * i)))) s =
             mld_poly_ntt (mld_poly_of x 0) i) /\
    (!i. i < 256
         ==> read (memory :> bytes32 (word_add sp (word (n + 1024 + 4 * i)))) s =
             mld_poly_ntt (mld_poly_of x 1) i) /\
    (!i. i < 256
         ==> read (memory :> bytes32 (word_add sp (word (n + 2048 + 4 * i)))) s =
             mld_poly_ntt (mld_poly_of x 2) i) /\
    (!i. i < 256
         ==> read (memory :> bytes32 (word_add sp (word (n + 3072 + 4 * i)))) s =
             mld_poly_ntt (mld_poly_of x 3) i)
    ==> !i. i < 1024
            ==> read (memory :> bytes32 (word_add sp (word (n + 4 * i)))) s =
                mld_polyvec_map mld_poly_ntt x i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?p k. p < 4 /\ k < 256 /\ i = 256 * p + k` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC [`i DIV 256`; `i MOD 256`] THEN
    MP_TAC(SPECL [`i:num`; `256`] DIVISION) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_SIMP_TAC[MLD_POLYVEC_MAP_COEFF] THEN
  SUBGOAL_THEN `p = 0 \/ p = 1 \/ p = 2 \/ p = 3` MP_TAC THENL
   [ASM_ARITH_TAC; DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC)] THEN
  REWRITE_TAC[ARITH_RULE `!n k. n + 4 * (256 * 0 + k) = n + 4 * k`;
              ARITH_RULE `!n k. n + 4 * (256 * 1 + k) = n + 1024 + 4 * k`;
              ARITH_RULE `!n k. n + 4 * (256 * 2 + k) = n + 2048 + 4 * k`;
              ARITH_RULE `!n k. n + 4 * (256 * 3 + k) = n + 3072 + 4 * k`] THEN
  ASM_SIMP_TAC[]);;

let PK44_NTT_JOIN4_RULE n s =
  CONV_RULE(REWRITE_CONV[ADD_ASSOC] THENC DEPTH_CONV NUM_ADD_CONV)
   (SPECL [`stackpointer:int64`; mk_small_numeral n; PK44_S1; s] PK44_NTT_JOIN4);;

let PK44_T0F =
  `mld_polyvec_pack 416 mld_polyt0_pack
     (mld_polyvec_map mld_poly_power2round_lo
       (mld_compute_t 4 mld_polyeta_unpack_2 96 r
         (mld_polyvec_map mld_poly_ntt
           (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. (skb:num->byte)(128 + j))))
         (\j. (skb:num->byte)(512 + j))))`;;

(*** The chunks of 16 bytes of the 1664 bytes of t0 in sk and in the buffer ***)
let PK44_CHUNKS_TAC base off fn sname =
  let sp = mk_var(sname,`:armstate`) in
  let offt = mk_small_numeral off in
  let b0 = mk_comb(mk_comb(`word_add:int64->int64->int64`,base),mk_comb(`word:num->int64`,offt)) in
  SUBGOAL_THEN
   (subst [base,`BASE:int64`; offt,`OFF:num`; fn,`FN:num->byte`; sp,`s:armstate`]
     `!k. k < 104 ==> read (memory :> bytes128 (word_add (BASE:int64) (word (OFF + 16 * k)))) s =
                      mld_chunk128 (FN:num->byte) k`)
   ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [b0; `1664`; fn; sp; `k:num`] BYTES128_OF_BYTES8) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
        REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN BETA_TAC THEN
        FIRST_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC;
        ASM_ARITH_TAC];
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      DISCH_THEN ACCEPT_TAC];
    ALL_TAC];;

let PK_CHKNORM_ENUM_CONV =
  let rec conv tm =
    match tm with
      Comb(Comb(Comb(Const("mld_polyvec_chknorm",_),n),_),_)
        when is_numeral n && dest_numeral n <>/ num 0 ->
        (RATOR_CONV(RATOR_CONV(RAND_CONV num_CONV)) THENC
         REWR_CONV(CONJUNCT2 mld_polyvec_chknorm) THENC LAND_CONV conv) tm
    | Comb(Comb(Comb(Const("mld_polyvec_chknorm",_),n),_),_)
        when is_numeral n -> REWR_CONV(CONJUNCT1 mld_polyvec_chknorm) tm
    | _ -> failwith "PK_CHKNORM_ENUM_CONV" in
  conv;;

let MLD_POLY_CHKNORM_LOCAL = prove
 (`!(a:num->int32) a' B.
        (!i. i < 256 ==> a i = a' i)
        ==> mld_poly_chknorm a B = mld_poly_chknorm a' B`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_poly_chknorm] THEN
  SUBGOAL_THEN
   `(?i. i < 256 /\ ival(word_sub (word_sub B (word 1)) (mld_ct_abs((a:num->int32) i))) < &0) <=>
    (?i. i < 256 /\ ival(word_sub (word_sub B (word 1)) (mld_ct_abs((a':num->int32) i))) < &0)`
   (fun th -> REWRITE_TAC[th]) THEN
  EQ_TAC THEN STRIP_TAC THEN EXISTS_TAC `i:num` THEN
  ASM_MESON_TAC[]);;

let PK44_S2_CHK_POLY = prove
 (`!k B. mld_poly_chknorm (mld_poly_of
           (mld_polyvec_unpack 96 mld_polyeta_unpack_2
             (\j. (skb:num->byte)(512 + j))) k) B =
         mld_poly_chknorm (mld_polyeta_unpack_2 (\j. skb(512 + 96 * k + j))) B`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MLD_POLY_CHKNORM_LOCAL THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[MLD_POLY_OF_POLYVEC; mld_polyvec_unpack]);;

let PK44_S2_CHK = prove
 (`!B. mld_polyvec_chknorm 4
         (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. (skb:num->byte)(512 + j))) B =
       word_or (word_or (word_or (word_or (word 0)
         (mld_poly_chknorm (mld_polyeta_unpack_2 (\j. skb(512 + j))) B))
         (mld_poly_chknorm (mld_polyeta_unpack_2 (\j. skb(608 + j))) B))
         (mld_poly_chknorm (mld_polyeta_unpack_2 (\j. skb(704 + j))) B))
         (mld_poly_chknorm (mld_polyeta_unpack_2 (\j. skb(800 + j))) B)`,
  GEN_TAC THEN
  CONV_TAC(LAND_CONV PK_CHKNORM_ENUM_CONV) THEN
  REWRITE_TAC[PK44_S2_CHK_POLY] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[ADD_CLAUSES; ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[]);;

let PK44_TEQ = prove
 (`mld_pk_from_sk_t 4 mld_polyeta_unpack_2 96 (skb:num->byte) =
   mld_compute_t 4 mld_polyeta_unpack_2 96 (mld_sk_rho skb)
    (mld_polyvec_map mld_poly_ntt
      (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. skb(128 + j))))
    (\j. skb(512 + j))`,
  CONV_TAC((REWRITE_CONV[mld_pk_from_sk_t; mld_sk_s1] THENC
            REWRITE_CONV[ADD_ASSOC] THENC NUM_REDUCE_CONV)) THEN
  REWRITE_TAC[]);;

let PK44_PKNUM = `num_of_bytelist (list_of_seq (mld_pk_from_sk_pk 4 mld_polyeta_unpack_2 96 (skb:num->byte)) 1312)`;;
let PK44_PKB = `mld_pk_from_sk_pk 4 mld_polyeta_unpack_2 96 (skb:num->byte)`;;

(*** The 1312 bytes of pk after compute_pack, in the state sname ***)
let PK44_PK_TAC sname =
  let sp = mk_var(sname,`:armstate`) in
  FIRST_ASSUM(fun th1 ->
    if lhs(concl th1) = subst [sp,`s:armstate`] `read (memory :> bytes128 pk) s` then
      FIRST_ASSUM(fun th2 ->
        if lhs(concl th2) = subst [sp,`s:armstate`] `read (memory :> bytes128 (word_add pk (word 16))) s`
        then ASSUME_TAC(MATCH_MP MLD_BYTES8_OF_CHUNKS2 (CONJ th1 th2))
        else NO_TAC)
    else NO_TAC) THEN
  FIRST_ASSUM(fun th1 ->
    if can (term_match [] (subst [sp,`s:armstate`]
          `!j. j < 32 ==> read (memory :> bytes8 (word_add pk (word j))) s = (skb:num->byte) j`)) (concl th1)
    then FIRST_ASSUM(fun th2 ->
      if can (term_match [] (subst [sp,`s:armstate`]
           `!j. j < 1280 ==> read (memory :> bytes8 (word_add pk (word(32 + j)))) s = (g:num->byte) j`)) (concl th2)
      then ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_ADD_CONV) (MATCH_MP MLD_BYTES8_JOIN (CONJ th1 th2)))
      else NO_TAC)
    else NO_TAC) THEN
  SUBGOAL_THEN
   (subst [sp,`s:armstate`]
     `read (memory :> bytes(pk,1312)) s =
      num_of_bytelist (list_of_seq (mld_pk_from_sk_pk 4 mld_polyeta_unpack_2 96 (skb:num->byte)) 1312)`)
   ASSUME_TAC THENL
   [MATCH_MP_TAC READ_BYTES_OF_BYTES8 THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [] (subst [sp,`s:armstate`] `!j. j < 1312 ==> read (memory :> bytes8 (word_add pk (word j))) s = (if j < 32 then (skb:num->byte) j else g (j - 32))`)) (concl th)
      then ASSUME_TAC(MP (SPEC `j:num` th) (ASSUME `j < 1312`)) else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[mld_pk_from_sk_pk; PK44_TEQ] THEN
    ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

let PK44_H = mk_comb(mk_comb(`mld_shake256_byte`,`1312`),
  `num_of_bytelist (list_of_seq (mld_pk_from_sk_pk 4 mld_polyeta_unpack_2 96 (skb:num->byte)) 1312)`);;

(*** The 64 bytes of tr_computed at sp + a as four chunks of 16 bytes ***)
let PK44_TRC_TAC a sname =
  let sp = mk_var(sname,`:armstate`) in
  let at = subst [mk_small_numeral a,`a:num`] `word_add stackpointer (word a):int64` in
  FIRST_ASSUM(fun th ->
    if can (term_match [] (subst [at,`a:int64`; sp,`s:armstate`]
         `read (memory :> bytes (a,64)) s = x`)) (concl th)
    then ASSUME_TAC(MATCH_MP BYTES8_OF_BYTES th) else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] (subst [at,`a:int64`; sp,`s:armstate`]
         `!j. j < 64 ==> read (memory :> bytes8 (word_add a (word j))) s = (f:num->byte) j`)) (concl th)
    then MAP_EVERY (fun i ->
      ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
        (CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
          (MP (SPECL [at; `64`; PK44_H; sp; mk_small_numeral i] BYTES128_OF_BYTES8)
              (CONJ th (EQT_ELIM(NUM_REDUCE_CONV
                 (subst [mk_small_numeral i,`i:num`] `16 * i + 16 <= 64`)))))))) (0--3)
    else NO_TAC);;

(*** The mask of the t0 comparison: the register X24 after the SHAKE256 ***)
let PK44_ABBREV_REG_TAC reg sname v =
  let sp = mk_var(sname,`:armstate`) in
  let l = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,mk_const(reg,[])),sp) in
  W(fun (asl,_) ->
    let th = snd(find (fun (_,th) -> try lhs(concl th) = l with Failure _ -> false) asl) in
    ABBREV_TAC (mk_eq(mk_var(v,`:int64`),rhs(concl th))));;

let PK44_MASK_RULE sname =
  let sp = mk_var(sname,`:armstate`) in
  let l = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,`X24`),sp) in
  W(fun (asl,_) ->
    let th = snd(find (fun (_,th) -> try lhs(concl th) = l with Failure _ -> false) asl) in
    let e = rhs(concl th) in
    let isf t = try fst(dest_const(fst(strip_comb t))) = "mld_or_fold" with _ -> false in
    let ors = find_terms (fun t -> try type_of t = `:int128` &&
       fst(dest_const(fst(strip_comb t))) = "word_or" && isf (lhand t) && isf (rand t)
       with _ -> false) e in
    let vt = hd ors in
    let g = genvar `:int128` in
    let eg = subst [g,vt] e in
    let tm = mk_forall(g,mk_eq(eg, mk_cond(mk_eq(g,`word 0:int128`),`word 0:int64`,`word 4294967295:int64`))) in
    let eth = SPEC vt (BITBLAST_RULE tm) in
    RULE_ASSUM_TAC(fun a -> if concl a = concl th then TRANS a eth else a));;

let PK_EVEN_ODD = prove
 (`!(P:num->bool) n. (!i. i < 2 * n ==> P i) <=>
                     (!k. k < n ==> P (2 * k)) /\ (!k. k < n ==> P (2 * k + 1))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN CONJ_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    STRIP_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(?k. k < n /\ i = 2 * k) \/ (?k. k < n /\ i = 2 * k + 1)`
     STRIP_ASSUME_TAC THENL
     [ASM_CASES_TAC `i MOD 2 = 0` THENL
       [DISJ1_TAC THEN EXISTS_TAC `i DIV 2` THEN ASM_ARITH_TAC;
        DISJ2_TAC THEN EXISTS_TAC `i DIV 2` THEN ASM_ARITH_TAC];
      ASM_MESON_TAC[]; ASM_MESON_TAC[]]]);;

let PK_T0EQ_GEN = prove
 (`!(t0f:num->byte) (skt:num->byte).
    mld_ct_memcmp t0f skt 1664 = word 0 <=>
    (mld_or_fold (\k. mld_chunk128 skt (2 * k)) (\k. mld_chunk128 t0f (2 * k)) 52 ||
     mld_or_fold (\k. mld_chunk128 skt (2 * k + 1)) (\k. mld_chunk128 t0f (2 * k + 1)) 52 =
     word 0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MLD_CT_MEMCMP_EQ_0; WORD_OR_EQ_0; MLD_OR_FOLD_EQ_0] THEN
  MP_TAC(SPECL [`\i. mld_chunk128 (skt:num->byte) i = mld_chunk128 t0f i`; `52`] PK_EVEN_ODD) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN BETA_TAC THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[MLD_CHUNK128_EQ] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  MESON_TAC[]);;

let PK_TREQ_GEN = prove
 (`!(f:num->byte) (g:num->byte).
    mld_ct_memcmp (\j. f (64 + j)) g 64 = word 0 <=>
    ((mld_chunk128 f 4 ^^ mld_chunk128 g 0) || (mld_chunk128 f 6 ^^ mld_chunk128 g 2)) ||
    (mld_chunk128 f 7 ^^ mld_chunk128 g 3) || (mld_chunk128 f 5 ^^ mld_chunk128 g 1) = word 0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MLD_CT_MEMCMP_EQ_0; WORD_OR_EQ_0; WORD_XOR_EQ_0] THEN
  MP_TAC(SPECL [`f:num->byte`; `g:num->byte`] MLD_CHUNKS4_EQ) THEN
  CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MESON_TAC[]);;

(*** valid as the code computes it ***)
let PK44_VALID_TH =
  CONV_RULE(RAND_CONV(REWRITE_CONV[PK44_TEQ; PK44_S2_CHK]))
  ((REWRITE_CONV[mld_pk_from_sk_valid; mld_sk_s1; mld_sk_s2] THENC
    REWRITE_CONV[ADD_ASSOC] THENC NUM_REDUCE_CONV)
   `mld_pk_from_sk_valid 4 4 2 mld_polyeta_unpack_2 96 (skb:num->byte)`);;

let PK44_TREQ = ISPECL [`skb:num->byte`; PK44_H] PK_TREQ_GEN;;

let pk_by_size tms =
  sort (fun a b -> String.length (string_of_term a) >= String.length (string_of_term b)) tms;;

(*** The branch on the checks of the end of pk_from_sk: the condition of the ***)
(*** PC at state sname (a test of the low byte of the OR of the checks) is   ***)
(*** the validity of the secret key                                          ***)
let PK44_CHECK_TAC sname =
  let pcl = mk_comb(`read PC`,mk_var(sname,`:armstate`)) in
  W(fun (asl,w) ->
    let pcth = snd(find (fun (_,th) -> try lhs(concl th) = pcl with Failure _ -> false) asl) in
    let cond = rand(rator(rator(rhs(concl pcth)))) in
    let isf t = try fst(dest_const(fst(strip_comb t))) = "mld_or_fold" with _ -> false in
    let hd_is c t = try fst(dest_const(fst(strip_comb t))) = c with Failure _ -> false in
    let xorv = hd(pk_by_size(find_terms (fun t -> type_of t = `:int128` && hd_is "word_xor" t && free_in `mld_shake256_byte` t && not(can (find_term (hd_is "word_zx")) t)) cond)) in
    let dor = hd(pk_by_size(find_terms (fun t -> type_of t = `:int128` && hd_is "word_or" t && free_in `mld_shake256_byte` t && not(can (find_term (hd_is "word_zx")) t)) cond)) in
    let folds = find_terms (fun t -> isf t && type_of t = `:int128`) cond in
    let f0 = el 0 (pk_by_size folds) in
    let chks = setify(find_terms (fun t -> type_of t = `:int32` && (hd_is "mld_poly_chknorm" t || hd_is "mld_polyvec_chknorm" t)) cond) in
    let atoms = [xorv; dor] @ folds @ chks in
    let mterm = hd(pk_by_size(find_terms (fun t -> type_of t = `:int64` && free_in dor t && not(free_in xorv t)) cond)) in
    let g0 = genvar `:int128` in
    let meq = SPEC dor (BITBLAST_RULE (mk_forall(g0,mk_eq(subst [g0,dor] mterm,
                mk_cond(mk_eq(g0,`word 0:int128`),`word 0:int64`,`word 4294967295:int64`))))) in
    let tm = mk_iff(cond, `mld_pk_from_sk_valid 4 4 2 mld_polyeta_unpack_2 96 (skb:num->byte)`) in
    let treq = mk_iff(mk_eq((mk_comb(mk_comb(`mld_ct_memcmp (\j. (skb:num->byte) (64 + j))`,PK44_H),`64`)),`word 0:byte`),
                       mk_eq(dor,`word 0:int128`)) in
    SUBGOAL_THEN treq (LABEL_TAC "TREQ") THENL
     [REWRITE_TAC[MLD_CT_MEMCMP_EQ_0; WORD_OR_EQ_0; WORD_XOR_EQ_0] THEN
      MP_TAC(SPECL [`skb:num->byte`; PK44_H] MLD_CHUNKS4_EQ) THEN
      CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CONV_TAC TAUT;
      ALL_TAC] THEN
    SUBGOAL_THEN tm (LABEL_TAC "CHECK") THENL
     [REWRITE_TAC[PK44_VALID_TH] THEN FIRST_ASSUM(fun eq -> if concl eq = `mld_sk_rho skb = r` then REWRITE_TAC[eq] else NO_TAC) THEN REWRITE_TAC[PK_T0EQ_GEN] THEN
      USE_THEN "TREQ" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[meq] THEN
      MAP_EVERY (fun t -> SPEC_TAC(t,genvar(type_of t))) atoms THEN
      REPEAT GEN_TAC THEN BITBLAST_TAC;
      ALL_TAC]);;

(*** Step to the return, with the calls of memset through the PLT ***)
let rec PK44_RUN_TAC execth fn adrplab allowed n (asl,w) =
  let off = pfs_pc_offset (pfs_current_pc (asl,w)) in
  if off < 0 then ALL_TAC (asl,w)
  else if off = layout "plt_memset" then
    (LIBC_PLT_TAC execth (n - 1) THEN
     PFS_LIBC_SAFE_CALL_TAC "H_MEMSET" execth
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
       `read X30 s`] (ref allowed) (n + 4) THEN
     PK44_RUN_TAC execth fn adrplab allowed (n + 5)) (asl,w)
  else
    (ARM_STEPS_TAC execth [n] THEN
     (if off = layout(fn ^ "_" ^ adrplab) then MLKEM_NATIVE_ADRP_TAC
      else ALL_TAC) THEN
     PFS_DECIDE_TAC THEN PK44_RUN_TAC execth fn adrplab allowed (n + 1)) (asl,w);;

(*** The end of a path: the postcondition, and the events ***)
let PK44_FINAL_TAC =
  TRY(FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes (pk,1312)) s = x`) (concl th)
    then ASSUME_TAC(MATCH_MP BYTES8_OF_BYTES th) else NO_TAC)) THEN
  PFS_FINAL_TAC;;

let PK44_CASE_TAC b =
  let s1 = b + 2720 and t0 = b + 32 and rho = b + 6976 and trc = b + 6848 in
  (KGP_SP_BOUNDS_TAC 12672) THEN
  (FULL_INIT_TAC THEN PK44_SK_CHUNKS_TAC THEN PK44_SK256_TAC) THEN
  (ARM_STEPS_TAC PK44_EXEC (1--10)) THEN
  PK44_BUF_TAC THEN
  (ARM_STEPS_TAC PK44_EXEC [11]) THEN
  (MAP_EVERY (fun n -> KGP_PROBE_TAC 12672 PK44_EXEC n) (12--17)) THEN
  (ARM_STEPS_TAC PK44_EXEC [18]) THEN
  (ARM_STEPS_TAC PK44_EXEC [19] THEN MLKEM_NATIVE_ADRP_TAC) THEN
  (ARM_STEPS_TAC PK44_EXEC (20--43)) THEN
  (PK44_UNPACK_CALL_TAC 128 44) THEN
  (ARM_STEPS_TAC PK44_EXEC (45--47)) THEN
  (PK44_UNPACK_CALL_TAC 224 48) THEN
  (ARM_STEPS_TAC PK44_EXEC (49--51)) THEN
  (PK44_UNPACK_CALL_TAC 320 52) THEN
  (ARM_STEPS_TAC PK44_EXEC (53--55)) THEN
  (PK44_UNPACK_CALL_TAC 416 56) THEN
  (ARM_STEPS_TAC PK44_EXEC (57--59)) THEN
  (MP_TAC(PK44_JOIN4_RULE s1 `s59:armstate`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC]) THEN
  (MAP_EVERY (fun p -> PK44_S1_SLICE_TAC s1 p "s59") (0--3)) THEN
  (PK44_CALL_TAC "H_CHKL" [`read X0 s`; PK44_S1; `read X1 s`; `pc:num`; `read SP s`; `read X30 s`] 60) THEN
  (ARM_STEPS_TAC PK44_EXEC (61--65)) THEN
  (PK44_UNPACK_CALL_TAC 512 66) THEN
  (ARM_STEPS_TAC PK44_EXEC (67--69)) THEN
  (PK44_CHK_LOOP_CALL_TAC 0 "X23" "X22" 70) THEN
  (ARM_STEPS_TAC PK44_EXEC (71--74)) THEN
  (PK44_UNPACK_CALL_TAC 608 75) THEN
  (ARM_STEPS_TAC PK44_EXEC (76--78)) THEN
  (PK44_CHK_LOOP_CALL_TAC 1 "X25" "X23" 79) THEN
  (ARM_STEPS_TAC PK44_EXEC (80--83)) THEN
  (PK44_UNPACK_CALL_TAC 704 84) THEN
  (ARM_STEPS_TAC PK44_EXEC (85--87)) THEN
  (PK44_CHK_LOOP_CALL_TAC 2 "X26" "X25" 88) THEN
  (ARM_STEPS_TAC PK44_EXEC (89--92)) THEN
  (PK44_UNPACK_CALL_TAC 800 93) THEN
  (ARM_STEPS_TAC PK44_EXEC (94--96)) THEN
  (PK44_CHK_LOOP_CALL_TAC 3 "X28" "X26" 97) THEN
  (ARM_STEPS_TAC PK44_EXEC (98--99)) THEN
  (PK44_NTT_CALL_TAC 0 100) THEN
  (ARM_STEPS_TAC PK44_EXEC (101--102)) THEN
  (PK44_NTT_CALL_TAC 1 103) THEN
  (ARM_STEPS_TAC PK44_EXEC (104--105)) THEN
  (PK44_NTT_CALL_TAC 2 106) THEN
  (ARM_STEPS_TAC PK44_EXEC (107--108)) THEN
  (PK44_NTT_CALL_TAC 3 109) THEN
  (ARM_STEPS_TAC PK44_EXEC (110--120)) THEN
  (MP_TAC(PK44_NTT_JOIN4_RULE s1 `s120:armstate`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC]) THEN
  (SUBGOAL_THEN `!j. j < 1024 ==> abs(ival(mld_polyvec_map mld_poly_ntt (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. (skb:num->byte)(128 + j))) j)) < &94279689` ASSUME_TAC THENL
        [MP_TAC(SPECL [`4`; `mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. (skb:num->byte)(128 + j))`] MLD_LAZY_POLYVEC_NTT_BOUND) THEN
         CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
         DISCH_THEN MATCH_MP_TAC THEN
         REWRITE_TAC[mld_polyvec_unpack; mld_polyvec; MLD_LAZY_ETA_UNPACK_BOUND];
         ALL_TAC]) THEN
  (PK44_BYTES_SLICE_TAC `!j. j < 384 ==> read(memory :> bytes8(word_add sk (word(512 + j)))) s120 = (skb:num->byte)(512 + j)`) THEN
  (MP_TAC(ISPECL [(parse_term(Printf.sprintf "word_add (stackpointer:int64) (word %d)" rho)); `skb:num->byte`; `s120:armstate`] MLD_BYTES32_OF_CHUNKS) THEN ANTS_TAC THENL [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN ASM_REWRITE_TAC[]; REWRITE_TAC[GSYM mld_sk_rho] THEN DISCH_THEN(fun th -> FIRST_ASSUM(fun eq -> if concl eq = `mld_sk_rho skb = r` then ASSUME_TAC(REWRITE_RULE[eq] th) else NO_TAC))]) THEN
  (PK44_CALL_TAC "H_CPT"
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `mld_polyvec_map mld_poly_ntt (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. (skb:num->byte)(128 + j)))`;
    `\j. (skb:num->byte)(512 + j)`; `r:num`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 121) THEN
  (ARM_STEPS_TAC PK44_EXEC (122--122)) THEN
  (ARM_STEPS_TAC PK44_EXEC [123] THEN MLKEM_NATIVE_ADRP_TAC) THEN
  (ARM_STEPS_TAC PK44_EXEC (124--129)) THEN
  (ARM_STEPS_TAC PK44_EXEC [130] THEN MLKEM_NATIVE_ADRP_TAC) THEN
  (ARM_STEPS_TAC PK44_EXEC (131--132)) THEN
  (ARM_STEPS_TAC PK44_EXEC [133] THEN MLKEM_NATIVE_ADRP_TAC) THEN
  (ARM_STEPS_TAC PK44_EXEC (134--135)) THEN
  (ARM_STEPS_TAC PK44_EXEC [136] THEN MLKEM_NATIVE_ADRP_TAC) THEN
  (ARM_STEPS_TAC PK44_EXEC (137--141)) THEN
  (PK44_CHUNKS_TAC `sk:int64` 896 `\j. (skb:num->byte) (896 + j)` "s141") THEN
  (PK44_CHUNKS_TAC `stackpointer:int64` t0 PK44_T0F "s141") THEN
  (PK44_CALL_TAC "H_CMP" [`sk:int64`; `read X27 s`; `mld_chunk128 (\j. (skb:num->byte) (896 + j))`; mk_comb(`mld_chunk128`,PK44_T0F); `pc:num`] 142) THEN
  (MAP_EVERY (fun r ->
  let q = mk_var("q"^r,`:int128`) in
  let rd = mk_comb(mk_comb(`read:(armstate,int128)component->armstate->int128`,mk_const("Q"^r,[])),`s142:armstate`) in
  SUBGOAL_THEN (mk_exists(q,mk_eq(rd,q))) STRIP_ASSUME_TAC THENL
   [EXISTS_TAC rd THEN REFL_TAC; ALL_TAC]) ["1";"2";"3";"4";"5";"6";"7";"16"]) THEN
  (ARM_STEPS_TAC PK44_EXEC (143--169)) THEN
  (PK44_PK_TAC "s169") THEN
  (PK44_ABBREV_REG_TAC "X27" "s169" "x27v") THEN
  (PK44_CALL_TAC "H_SHAKE" [`read SP s`; `read X19 s`; PK44_PKNUM; `read X23 s`; `read X25 s`; `read X27 s`; `read X28 s`; `read X0 s`; `pc:num`] 170) THEN
  (PK44_MASK_RULE "s170") THEN
  (PK44_TRC_TAC trc "s170") THEN
  (ARM_STEPS_TAC PK44_EXEC (171--215)) THEN
  (PK44_CHECK_TAC "s215") THEN
  (USE_THEN "CHECK" (fun th -> RULE_ASSUM_TAC(fun t -> if pfs_pcev t then REWRITE_RULE[th] t else t))) THEN
  (PFS_CASES_TAC PK44_VALID) THEN
  (PK44_RUN_TAC PK44_EXEC "mldsa44_pk_from_sk" "adrp6" PK44_ALLOWED 216) THEN
  PK44_FINAL_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together.                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN PK44_CALLEES_TAC THEN
  CONCRETIZE_F_EVENTS_TAC PK44_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  PK44_SETUP_TAC THEN
  ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [REWRITE_TAC[ASSUME `aligned 32 (stackpointer:int64)`] THEN
    PK44_CASE_TAC 5344;
    REWRITE_TAC[ASSUME `~aligned 32 (stackpointer:int64)`] THEN
    PK44_CASE_TAC 5328]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL)
        th)));;
