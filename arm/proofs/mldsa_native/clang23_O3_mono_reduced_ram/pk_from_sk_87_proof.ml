(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The public key of a secret key: the proof (see pk_from_sk_87_spec.ml).   *)
(* clang has inlined the checks of s2, the comparison of t0 and the hash of  *)
(* the public key into the function, which the proof composes with the       *)
(* theorems for its callees and for those parts (inline_pk_from_sk_87.ml),   *)
(* in the order of the code, from the prologue (with the probe of the stack  *)
(* and the buffers 32-byte aligned at stackpointer + b, b = 5344 or 5328     *)
(* by the alignment of the stack pointer) to the return.                     *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/pk_from_sk_87_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyeta_unpack_87_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_ntt_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/lazy_eq_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_probe.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_pk_from_sk_87.ml";;
needs "arm/proofs/utils/mldsa_native_verify.ml";;
needs "arm/proofs/utils/mldsa_native_top.ml";;
needs "arm/proofs/utils/mldsa_native_wrap.ml";;

let PK87_EXEC = MLDSA_NATIVE_PK_FROM_SK_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;
let PK87_MC = mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc;;

let PK87_ALLOWED =
  [`pk:int64`; `sk:int64`; `skb:num->byte`; `guard:int64`; `mf:int64`;
   `mc:int64`; `pc:num`; `stackpointer:int64`; `returnaddress:int64`;
   `r:num`];;

let PK87_ARGS = "pk sk r valid guard mf mc pc stackpointer returnaddress";;

let PK87_LAMBDA =
  "\\(pk:int64) (sk:int64) (r:num) (valid:bool) (guard:int64) (mf:int64) " ^
  "(mc:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).";;

let PK87_TEMPLATE =
  let f n = "(f_ev_" ^ n ^ " " ^ PK87_ARGS ^ ")" in
  parse_term(PK87_LAMBDA ^ " if aligned 32 stackpointer " ^
    "then (if valid then " ^ f "av" ^ " else " ^ f "ai" ^ ") " ^
    "else (if valid then " ^ f "uv" ^ " else " ^ f "ui" ^ ") " ^
    ":(uarch_event)list");;

let PK87_VALID = `mld_pk_from_sk_valid 8 7 2 mld_polyeta_unpack_2 96 skb`;;

let PK87_CPT =
  MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL;;

let PK87_CALLEES_TAC =
  FIRST_ASSUM(fun th ->
    let m1 = CONJUNCT1 th in
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] m1)
     "H_MEMSET" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP PK87_CPT th) "H_CPT") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYETA_UNPACK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
   "H_UNPACK" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYVECL_CHKNORM_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
   "H_CHKL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
   "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC KG_MEMCMP87 "H_CMP" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC KG_SHAKE87 "H_SHAKE" THEN
  MAP_EVERY (fun (th,k) ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC th ("H_L"^string_of_int k))
   (zip PK87_CHK_THS (2--9));;

let PK87_SETUP_TAC =
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst PK87_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 17408):int64)` THEN
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
let PK87_SK_CHUNKS_TAC =
  W(fun (asl,w) ->
    let skf = find (fun th -> can (term_match []
       `!j. j < 4896 ==> read(memory :> bytes8(word_add sk (word j))) s = skb j`) (concl th)) (map snd asl) in
    MAP_EVERY (fun m ->
      let th = MP (SPECL [`sk:int64`; `4896`; `skb:num->byte`;
                          rand(lhand(rand(snd(dest_forall(concl skf)))));
                          mk_small_numeral m] BYTES128_OF_BYTES8)
                  (CONJ skf (EQT_ELIM(NUM_REDUCE_CONV
                     (subst [mk_small_numeral m,`m:num`] `16 * m + 16 <= 4896`)))) in
      ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV THENC
                           REWRITE_CONV[WORD_ADD_0]) th)) (0--7));;

let PK87_SK256_TAC =
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

let PK87_BUF_TAC =
  FIRST_ASSUM(fun a16 ->
    if concl a16 <> `aligned 16 (stackpointer:int64)` then NO_TAC else
    let th = MP (SPEC `stackpointer:int64` (MLD_WRAP_BUFFER_RULE `5344`)) a16 in
    FIRST_ASSUM(fun cth ->
      if concl cth = `aligned 32 (stackpointer:int64)` ||
         concl cth = `~aligned 32 (stackpointer:int64)`
      then RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_RULE[cth] th])
      else NO_TAC));;

let PK87_CALL_TAC name ilist n =
  FULL_CALL_TAC PK87_MC PK87_EXEC name ilist PK87_ALLOWED n;;

let PK87_BYTES_SLICE_TAC tm =
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC];;

(*** A call of polyeta_unpack on the 96 bytes of sk at off, after state n-1 ***)
let PK87_UNPACK_CALL_TAC off n =
  let s = mk_var("s"^string_of_int(n-1),`:armstate`) in
  PK87_BYTES_SLICE_TAC (subst [mk_small_numeral off,`off:num`; s,`s:armstate`]
   `!j. j < 96 ==> read(memory :> bytes8(word_add sk (word(off + j)))) s =
                   (skb:num->byte)(off + j)`) THEN
  PK87_CALL_TAC "H_UNPACK"
   [`read X0 s`; `read X1 s`;
    subst [mk_small_numeral off,`off:num`] `\j. (skb:num->byte)(off + j)`;
    `pc:num`; `read SP s`; `read X30 s`] n;;

(*** Restate a register fact as the form of the precondition of a lemma ***)
let PK87_PATCH_TAC (patches:(term*term) list) =
  RULE_ASSUM_TAC(fun th ->
    try let c = concl th in
        let (l,r) = dest_eq c in
        let (_,nr) = find (fun (t,_) -> t = l) patches in
        let eq = prove(mk_eq(r,nr),FIRST[CONV_TAC WORD_REDUCE_CONV THEN NO_TAC; CONV_TAC WORD_RULE]) in
        TRANS th eq
    with Failure _ -> th);;

(*** A loop of the norm check of poly k of s2 ***)
let PK87_CHK_LOOP_CALL_TAC k areg accreg n =
  let sp = mk_var("s"^string_of_int(n-1),`:armstate`) in
  let rd r = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,mk_const(r,[])),sp) in
  PK87_PATCH_TAC [rd "X9", `word_zx (word_sub (word 3:int32) (word 1)):int64`;
                  rd accreg, `word_zx (word 0:int32):int64`] THEN
  PK87_CALL_TAC ("H_L"^string_of_int(k+2))
   [mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,mk_const(areg,[])),`s:armstate`);
    subst [mk_small_numeral(800 + 96 * k),`off:num`]
      `mld_polyeta_unpack_2 (\j. (skb:num->byte) (off + j))`;
    `word 3:int32`; `word 0:int32`; `pc:num`] n;;

(*** The four polynomials of s1 as slices of the vector, in the state sname ***)
let PK87_S1_SLICE_TAC s1 p sname =
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
           `!i. i < 1792 ==> read (memory :> bytes32 (word_add stackpointer (word (S1 + 4 * i)))) s = x i`)) (concl th)
      then MP_TAC(SPEC (subst [mk_small_numeral p,`p:num`] `256 * p + j`) th) else NO_TAC) THEN
    ANTS_TAC THENL [FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `j < 256`)) THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE (subst [mk_small_numeral s1,`S1:num`; mk_small_numeral off,`off:num`; mk_small_numeral p,`p:num`]
      `S1 + 4 * (256 * p + j) = off + 4 * j`)] THEN
    DISCH_THEN ACCEPT_TAC;
    ALL_TAC];;

(*** The NTT of poly p of s1, in place ***)
let PK87_NTT_CALL_TAC p n =
  PK87_CALL_TAC "H_NTT"
   [`read X0 s`; subst [mk_small_numeral p,`p:num`] `mld_poly_of (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. (skb:num->byte) (128 + j))) p`;
    `pc:num`; `read SP s`; `read X30 s`] n;;

let PK87_JOIN = prove
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
             mld_polyeta_unpack_2 (\j. b (416 + j)) i) /\
    (!i. i < 256
         ==> read (memory :> bytes32 (word_add sp (word (n + 4096 + 4 * i)))) s =
             mld_polyeta_unpack_2 (\j. b (512 + j)) i) /\
    (!i. i < 256
         ==> read (memory :> bytes32 (word_add sp (word (n + 5120 + 4 * i)))) s =
             mld_polyeta_unpack_2 (\j. b (608 + j)) i) /\
    (!i. i < 256
         ==> read (memory :> bytes32 (word_add sp (word (n + 6144 + 4 * i)))) s =
             mld_polyeta_unpack_2 (\j. b (704 + j)) i)
    ==> !i. i < 1792
            ==> read (memory :> bytes32 (word_add sp (word (n + 4 * i)))) s =
                mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. b(128 + j)) i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[mld_polyvec_unpack; mld_polyvec] THEN
  SUBGOAL_THEN `?p k. p < 7 /\ k < 256 /\ i = 256 * p + k` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC [`i DIV 256`; `i MOD 256`] THEN
    MP_TAC(SPECL [`i:num`; `256`] DIVISION) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_SIMP_TAC[DIVMOD_CHUNK] THEN
  SUBGOAL_THEN `p = 0 \/ p = 1 \/ p = 2 \/ p = 3 \/ p = 4 \/ p = 5 \/ p = 6` MP_TAC THENL
   [ASM_ARITH_TAC; DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC)] THEN
  REWRITE_TAC[ARITH_RULE `!n k. n + 4 * (256 * 0 + k) = n + 4 * k`;
              ARITH_RULE `!n k. n + 4 * (256 * 1 + k) = n + 1024 + 4 * k`;
              ARITH_RULE `!n k. n + 4 * (256 * 2 + k) = n + 2048 + 4 * k`;
              ARITH_RULE `!n k. n + 4 * (256 * 3 + k) = n + 3072 + 4 * k`;
              ARITH_RULE `!n k. n + 4 * (256 * 4 + k) = n + 4096 + 4 * k`;
              ARITH_RULE `!n k. n + 4 * (256 * 5 + k) = n + 5120 + 4 * k`;
              ARITH_RULE `!n k. n + 4 * (256 * 6 + k) = n + 6144 + 4 * k`;
              ARITH_RULE `!t. 128 + 96 * 0 + t = 128 + t`;
              ARITH_RULE `!t. 128 + 96 * 1 + t = 224 + t`;
              ARITH_RULE `!t. 128 + 96 * 2 + t = 320 + t`;
              ARITH_RULE `!t. 128 + 96 * 3 + t = 416 + t`;
              ARITH_RULE `!t. 128 + 96 * 4 + t = 512 + t`;
              ARITH_RULE `!t. 128 + 96 * 5 + t = 608 + t`;
              ARITH_RULE `!t. 128 + 96 * 6 + t = 704 + t`] THEN
  ASM_SIMP_TAC[]);;


let PK87_S1 = `mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. (skb:num->byte)(128 + j))`;;

let PK87_JOIN_RULE n s =
  CONV_RULE(REWRITE_CONV[ADD_ASSOC] THENC DEPTH_CONV NUM_ADD_CONV)
   (SPECL [`stackpointer:int64`; mk_small_numeral n; `skb:num->byte`; s] PK87_JOIN);;

let PK87_NTT_JOIN = prove
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
             mld_poly_ntt (mld_poly_of x 3) i) /\
    (!i. i < 256
         ==> read (memory :> bytes32 (word_add sp (word (n + 4096 + 4 * i)))) s =
             mld_poly_ntt (mld_poly_of x 4) i) /\
    (!i. i < 256
         ==> read (memory :> bytes32 (word_add sp (word (n + 5120 + 4 * i)))) s =
             mld_poly_ntt (mld_poly_of x 5) i) /\
    (!i. i < 256
         ==> read (memory :> bytes32 (word_add sp (word (n + 6144 + 4 * i)))) s =
             mld_poly_ntt (mld_poly_of x 6) i)
    ==> !i. i < 1792
            ==> read (memory :> bytes32 (word_add sp (word (n + 4 * i)))) s =
                mld_polyvec_map mld_poly_ntt x i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?p k. p < 7 /\ k < 256 /\ i = 256 * p + k` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC [`i DIV 256`; `i MOD 256`] THEN
    MP_TAC(SPECL [`i:num`; `256`] DIVISION) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_SIMP_TAC[MLD_POLYVEC_MAP_COEFF] THEN
  SUBGOAL_THEN `p = 0 \/ p = 1 \/ p = 2 \/ p = 3 \/ p = 4 \/ p = 5 \/ p = 6` MP_TAC THENL
   [ASM_ARITH_TAC; DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC)] THEN
  REWRITE_TAC[ARITH_RULE `!n k. n + 4 * (256 * 0 + k) = n + 4 * k`;
              ARITH_RULE `!n k. n + 4 * (256 * 1 + k) = n + 1024 + 4 * k`;
              ARITH_RULE `!n k. n + 4 * (256 * 2 + k) = n + 2048 + 4 * k`;
              ARITH_RULE `!n k. n + 4 * (256 * 3 + k) = n + 3072 + 4 * k`;
              ARITH_RULE `!n k. n + 4 * (256 * 4 + k) = n + 4096 + 4 * k`;
              ARITH_RULE `!n k. n + 4 * (256 * 5 + k) = n + 5120 + 4 * k`;
              ARITH_RULE `!n k. n + 4 * (256 * 6 + k) = n + 6144 + 4 * k`] THEN
  ASM_SIMP_TAC[]);;


let PK87_NTT_JOIN_RULE n s =
  CONV_RULE(REWRITE_CONV[ADD_ASSOC] THENC DEPTH_CONV NUM_ADD_CONV)
   (SPECL [`stackpointer:int64`; mk_small_numeral n; PK87_S1; s] PK87_NTT_JOIN);;

let PK87_T0F =
  `mld_polyvec_pack 416 mld_polyt0_pack
     (mld_polyvec_map mld_poly_power2round_lo
       (mld_compute_t 7 mld_polyeta_unpack_2 96 r
         (mld_polyvec_map mld_poly_ntt
           (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. (skb:num->byte)(128 + j))))
         (\j. (skb:num->byte)(800 + j))))`;;

(*** The chunks of 16 bytes of the 3328 bytes of t0 in sk and in the buffer ***)
let PK87_CHUNKS_TAC base off fn sname =
  let sp = mk_var(sname,`:armstate`) in
  let offt = mk_small_numeral off in
  let b0 = mk_comb(mk_comb(`word_add:int64->int64->int64`,base),mk_comb(`word:num->int64`,offt)) in
  SUBGOAL_THEN
   (subst [base,`BASE:int64`; offt,`OFF:num`; fn,`FN:num->byte`; sp,`s:armstate`]
     `!k. k < 208 ==> read (memory :> bytes128 (word_add (BASE:int64) (word (OFF + 16 * k)))) s =
                      mld_chunk128 (FN:num->byte) k`)
   ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [b0; `3328`; fn; sp; `k:num`] BYTES128_OF_BYTES8) THEN
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

let PK87_S2_CHK_POLY = prove
 (`!k B. mld_poly_chknorm (mld_poly_of
           (mld_polyvec_unpack 96 mld_polyeta_unpack_2
             (\j. (skb:num->byte)(800 + j))) k) B =
         mld_poly_chknorm (mld_polyeta_unpack_2 (\j. skb(800 + 96 * k + j))) B`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MLD_POLY_CHKNORM_LOCAL THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[MLD_POLY_OF_POLYVEC; mld_polyvec_unpack]);;

let PK87_S2_CHK = prove
 (`!B. mld_polyvec_chknorm 8
         (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. (skb:num->byte)(800 + j))) B =
       word_or (word_or (word_or (word_or (word_or (word_or (word_or (word_or (word 0)
         (mld_poly_chknorm (mld_polyeta_unpack_2 (\j. skb(800 + j))) B))
         (mld_poly_chknorm (mld_polyeta_unpack_2 (\j. skb(896 + j))) B))
         (mld_poly_chknorm (mld_polyeta_unpack_2 (\j. skb(992 + j))) B))
         (mld_poly_chknorm (mld_polyeta_unpack_2 (\j. skb(1088 + j))) B))
         (mld_poly_chknorm (mld_polyeta_unpack_2 (\j. skb(1184 + j))) B))
         (mld_poly_chknorm (mld_polyeta_unpack_2 (\j. skb(1280 + j))) B))
         (mld_poly_chknorm (mld_polyeta_unpack_2 (\j. skb(1376 + j))) B))
         (mld_poly_chknorm (mld_polyeta_unpack_2 (\j. skb(1472 + j))) B)`,
  GEN_TAC THEN
  CONV_TAC(LAND_CONV PK_CHKNORM_ENUM_CONV) THEN
  REWRITE_TAC[PK87_S2_CHK_POLY] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[ADD_CLAUSES; ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[]);;


let PK87_TEQ = prove
 (`mld_pk_from_sk_t 7 mld_polyeta_unpack_2 96 (skb:num->byte) =
   mld_compute_t 7 mld_polyeta_unpack_2 96 (mld_sk_rho skb)
    (mld_polyvec_map mld_poly_ntt
      (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. skb(128 + j))))
    (\j. skb(800 + j))`,
  CONV_TAC((REWRITE_CONV[mld_pk_from_sk_t; mld_sk_s1] THENC
            REWRITE_CONV[ADD_ASSOC] THENC NUM_REDUCE_CONV)) THEN
  REWRITE_TAC[]);;

let PK87_PKNUM = `num_of_bytelist (list_of_seq (mld_pk_from_sk_pk 7 mld_polyeta_unpack_2 96 (skb:num->byte)) 2592)`;;
let PK87_PKB = `mld_pk_from_sk_pk 7 mld_polyeta_unpack_2 96 (skb:num->byte)`;;

(*** The 2592 bytes of pk after compute_pack, in the state sname ***)
let PK87_PK_TAC sname =
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
           `!j. j < 2560 ==> read (memory :> bytes8 (word_add pk (word(32 + j)))) s = (g:num->byte) j`)) (concl th2)
      then ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_ADD_CONV) (MATCH_MP MLD_BYTES8_JOIN (CONJ th1 th2)))
      else NO_TAC)
    else NO_TAC) THEN
  SUBGOAL_THEN
   (subst [sp,`s:armstate`]
     `read (memory :> bytes(pk,2592)) s =
      num_of_bytelist (list_of_seq (mld_pk_from_sk_pk 7 mld_polyeta_unpack_2 96 (skb:num->byte)) 2592)`)
   ASSUME_TAC THENL
   [MATCH_MP_TAC READ_BYTES_OF_BYTES8 THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [] (subst [sp,`s:armstate`] `!j. j < 2592 ==> read (memory :> bytes8 (word_add pk (word j))) s = (if j < 32 then (skb:num->byte) j else g (j - 32))`)) (concl th)
      then ASSUME_TAC(MP (SPEC `j:num` th) (ASSUME `j < 2592`)) else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[mld_pk_from_sk_pk; PK87_TEQ] THEN
    ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

let PK87_H = mk_comb(mk_comb(`mld_shake256_byte`,`2592`),
  `num_of_bytelist (list_of_seq (mld_pk_from_sk_pk 7 mld_polyeta_unpack_2 96 (skb:num->byte)) 2592)`);;

(*** The 64 bytes of tr_computed at sp + a as four chunks of 16 bytes ***)
let PK87_TRC_TAC a sname =
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
          (MP (SPECL [at; `64`; PK87_H; sp; mk_small_numeral i] BYTES128_OF_BYTES8)
              (CONJ th (EQT_ELIM(NUM_REDUCE_CONV
                 (subst [mk_small_numeral i,`i:num`] `16 * i + 16 <= 64`)))))))) (0--3)
    else NO_TAC);;

(*** The mask of the t0 comparison: the register X21 before the SHAKE256 ***)
let PK87_ABBREV_REG_TAC reg sname v =
  let sp = mk_var(sname,`:armstate`) in
  let l = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,mk_const(reg,[])),sp) in
  W(fun (asl,_) ->
    let th = snd(find (fun (_,th) -> try lhs(concl th) = l with Failure _ -> false) asl) in
    ABBREV_TAC (mk_eq(mk_var(v,`:int64`),rhs(concl th))));;

let PK87_MASK_RULE sname =
  let sp = mk_var(sname,`:armstate`) in
  let l = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,`X21`),sp) in
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
    let tm = mk_forall(g,mk_eq(eg, mk_comb(`word_zx:int32->int64`, mk_comb(mk_comb(`word_xor:int32->int32->int32`, mk_cond(mk_eq(g,`word 0:int128`),`word 0:int32`,`word 4294967295:int32`)), `word_zx (x9v:int64):int32`)))) in
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
    mld_ct_memcmp t0f skt 3328 = word 0 <=>
    (mld_or_fold (\k. mld_chunk128 skt (2 * k)) (\k. mld_chunk128 t0f (2 * k)) 104 ||
     mld_or_fold (\k. mld_chunk128 skt (2 * k + 1)) (\k. mld_chunk128 t0f (2 * k + 1)) 104 =
     word 0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MLD_CT_MEMCMP_EQ_0; WORD_OR_EQ_0; MLD_OR_FOLD_EQ_0] THEN
  MP_TAC(SPECL [`\i. mld_chunk128 (skt:num->byte) i = mld_chunk128 t0f i`; `104`] PK_EVEN_ODD) THEN
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
let PK87_VALID_TH =
  CONV_RULE(RAND_CONV(REWRITE_CONV[PK87_TEQ; PK87_S2_CHK]))
  ((REWRITE_CONV[mld_pk_from_sk_valid; mld_sk_s1; mld_sk_s2] THENC
    REWRITE_CONV[ADD_ASSOC] THENC NUM_REDUCE_CONV)
   `mld_pk_from_sk_valid 8 7 2 mld_polyeta_unpack_2 96 (skb:num->byte)`);;

let PK87_TREQ = ISPECL [`skb:num->byte`; PK87_H] PK_TREQ_GEN;;

let pk_by_size tms =
  sort (fun a b -> String.length (string_of_term a) >= String.length (string_of_term b)) tms;;

(*** The branch on the checks of the end of pk_from_sk: the condition of the ***)
(*** PC at state sname (a test of the low byte of the OR of the checks) is   ***)
(*** the validity of the secret key                                          ***)
let PK87_CHECK_TAC sname =
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
    let x9v = `x9v:int64` in
    let atoms = [xorv; dor; x9v] @ folds @ chks in
    let mterm = hd(pk_by_size(find_terms (fun t -> type_of t = `:int64` && free_in dor t && not(free_in xorv t)) cond)) in
    let g0 = genvar `:int128` in
    let meq = SPEC dor (BITBLAST_RULE (mk_forall(g0,mk_eq(subst [g0,dor] mterm,
                mk_cond(mk_eq(g0,`word 0:int128`),`word 0:int64`,`word 4294967295:int64`))))) in
    let tm = mk_iff(cond, `mld_pk_from_sk_valid 8 7 2 mld_polyeta_unpack_2 96 (skb:num->byte)`) in
    let treq = mk_iff(mk_eq((mk_comb(mk_comb(`mld_ct_memcmp (\j. (skb:num->byte) (64 + j))`,PK87_H),`64`)),`word 0:byte`),
                       mk_eq(dor,`word 0:int128`)) in
    SUBGOAL_THEN treq (LABEL_TAC "TREQ") THENL
     [REWRITE_TAC[MLD_CT_MEMCMP_EQ_0; WORD_OR_EQ_0; WORD_XOR_EQ_0] THEN
      MP_TAC(SPECL [`skb:num->byte`; PK87_H] MLD_CHUNKS4_EQ) THEN
      CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CONV_TAC TAUT;
      ALL_TAC] THEN
    SUBGOAL_THEN tm (LABEL_TAC "CHECK") THENL
     [REWRITE_TAC[PK87_VALID_TH] THEN FIRST_ASSUM(fun eq -> if concl eq = `mld_sk_rho skb = r` then REWRITE_TAC[eq] else NO_TAC) THEN REWRITE_TAC[PK_T0EQ_GEN] THEN
      USE_THEN "TREQ" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[meq] THEN
      MAP_EVERY (fun t -> SPEC_TAC(t,genvar(type_of t))) atoms THEN
      REPEAT GEN_TAC THEN BITBLAST_TAC;
      ALL_TAC]);;

(*** Step to the return, with the calls of memset through the PLT ***)
let rec PK87_RUN_TAC execth fn adrplab allowed n (asl,w) =
  let off = pfs_pc_offset (pfs_current_pc (asl,w)) in
  if off < 0 then ALL_TAC (asl,w)
  else if off = layout "plt_memset" then
    (LIBC_PLT_TAC execth (n - 1) THEN
     PFS_LIBC_SAFE_CALL_TAC "H_MEMSET" execth
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
       `read X30 s`] (ref allowed) (n + 4) THEN
     PK87_RUN_TAC execth fn adrplab allowed (n + 5)) (asl,w)
  else
    (ARM_STEPS_TAC execth [n] THEN
     (if off = layout(fn ^ "_" ^ adrplab) then MLKEM_NATIVE_ADRP_TAC
      else ALL_TAC) THEN
     PFS_DECIDE_TAC THEN PK87_RUN_TAC execth fn adrplab allowed (n + 1)) (asl,w);;

(*** The end of a path: the postcondition, and the events ***)
let PK87_FINAL_TAC =
  TRY(FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes (pk,2592)) s = x`) (concl th)
    then ASSUME_TAC(MATCH_MP BYTES8_OF_BYTES th) else NO_TAC)) THEN
  PFS_FINAL_TAC;;

let PK87_CASE_TAC b =
  let s1 = b + 4384 and t0 = b + 32 and rho = b + 11712 and trc = b + 11584 in
  (KGP_SP_BOUNDS_TAC 17408) THEN
  (FULL_INIT_TAC THEN PK87_SK_CHUNKS_TAC THEN PK87_SK256_TAC) THEN
  (ARM_STEPS_TAC PK87_EXEC (1--10)) THEN
  PK87_BUF_TAC THEN
  (ARM_STEPS_TAC PK87_EXEC [11]) THEN
  (MAP_EVERY (fun n -> KGP_PROBE_TAC 17408 PK87_EXEC n) (12--21)) THEN
  (ARM_STEPS_TAC PK87_EXEC [22]) THEN
  (ARM_STEPS_TAC PK87_EXEC [23] THEN MLKEM_NATIVE_ADRP_TAC) THEN
  (ARM_STEPS_TAC PK87_EXEC (24--47)) THEN
  (PK87_UNPACK_CALL_TAC 128 48) THEN
  (ARM_STEPS_TAC PK87_EXEC (49--51)) THEN
  (PK87_UNPACK_CALL_TAC 224 52) THEN
  (ARM_STEPS_TAC PK87_EXEC (53--55)) THEN
  (PK87_UNPACK_CALL_TAC 320 56) THEN
  (ARM_STEPS_TAC PK87_EXEC (57--59)) THEN
  (PK87_UNPACK_CALL_TAC 416 60) THEN
  (ARM_STEPS_TAC PK87_EXEC (61--63)) THEN
  (PK87_UNPACK_CALL_TAC 512 64) THEN
  (ARM_STEPS_TAC PK87_EXEC (65--68)) THEN
  (PK87_UNPACK_CALL_TAC 608 69) THEN
  (ARM_STEPS_TAC PK87_EXEC (70--73)) THEN
  (PK87_UNPACK_CALL_TAC 704 74) THEN
  (ARM_STEPS_TAC PK87_EXEC (75--78)) THEN
  (MP_TAC(PK87_JOIN_RULE s1 `s78:armstate`) THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC; DISCH_TAC]) THEN
  (MAP_EVERY (fun p -> PK87_S1_SLICE_TAC s1 p "s78") (0--6)) THEN
  (PK87_CALL_TAC "H_CHKL" [`read X0 s`; PK87_S1; `read X1 s`; `pc:num`; `read SP s`; `read X30 s`] 79) THEN
  (ARM_STEPS_TAC PK87_EXEC (80--84)) THEN
  (PK87_UNPACK_CALL_TAC 800 85) THEN
  (ARM_STEPS_TAC PK87_EXEC (86--88)) THEN
  (PK87_CHK_LOOP_CALL_TAC 0 "X20" "X13" 89) THEN
  (ARM_STEPS_TAC PK87_EXEC (90--94)) THEN
  (PK87_UNPACK_CALL_TAC 896 95) THEN
  (ARM_STEPS_TAC PK87_EXEC (96--98)) THEN
  (PK87_CHK_LOOP_CALL_TAC 1 "X20" "X24" 99) THEN
  (ARM_STEPS_TAC PK87_EXEC (100--103)) THEN
  (PK87_UNPACK_CALL_TAC 992 104) THEN
  (ARM_STEPS_TAC PK87_EXEC (105--107)) THEN
  (PK87_CHK_LOOP_CALL_TAC 2 "X20" "X25" 108) THEN
  (ARM_STEPS_TAC PK87_EXEC (109--112)) THEN
  (PK87_UNPACK_CALL_TAC 1088 113) THEN
  (ARM_STEPS_TAC PK87_EXEC (114--116)) THEN
  (PK87_CHK_LOOP_CALL_TAC 3 "X20" "X26" 117) THEN
  (ARM_STEPS_TAC PK87_EXEC (118--121)) THEN
  (PK87_UNPACK_CALL_TAC 1184 122) THEN
  (ARM_STEPS_TAC PK87_EXEC (123--125)) THEN
  (PK87_CHK_LOOP_CALL_TAC 4 "X20" "X27" 126) THEN
  (ARM_STEPS_TAC PK87_EXEC (127--130)) THEN
  (PK87_UNPACK_CALL_TAC 1280 131) THEN
  (ARM_STEPS_TAC PK87_EXEC (132--134)) THEN
  (PK87_CHK_LOOP_CALL_TAC 5 "X20" "X28" 135) THEN
  (ARM_STEPS_TAC PK87_EXEC (136--139)) THEN
  (PK87_UNPACK_CALL_TAC 1376 140) THEN
  (ARM_STEPS_TAC PK87_EXEC (141--143)) THEN
  (PK87_CHK_LOOP_CALL_TAC 6 "X22" "X20" 144) THEN
  (ARM_STEPS_TAC PK87_EXEC (145--148)) THEN
  (PK87_UNPACK_CALL_TAC 1472 149) THEN
  (ARM_STEPS_TAC PK87_EXEC (150--152)) THEN
  (PK87_CHK_LOOP_CALL_TAC 7 "X22" "X23" 153) THEN
  (ARM_STEPS_TAC PK87_EXEC (154--156)) THEN
  (PK87_NTT_CALL_TAC 0 157) THEN
  (ARM_STEPS_TAC PK87_EXEC (158--161)) THEN
  (PK87_NTT_CALL_TAC 1 162) THEN
  (ARM_STEPS_TAC PK87_EXEC (163--164)) THEN
  (PK87_NTT_CALL_TAC 2 165) THEN
  (ARM_STEPS_TAC PK87_EXEC (166--167)) THEN
  (PK87_NTT_CALL_TAC 3 168) THEN
  (ARM_STEPS_TAC PK87_EXEC (169--170)) THEN
  (PK87_NTT_CALL_TAC 4 171) THEN
  (ARM_STEPS_TAC PK87_EXEC (172--174)) THEN
  (PK87_NTT_CALL_TAC 5 175) THEN
  (ARM_STEPS_TAC PK87_EXEC (176--178)) THEN
  (PK87_NTT_CALL_TAC 6 179) THEN
  (ARM_STEPS_TAC PK87_EXEC (180--191)) THEN
  (MP_TAC(PK87_NTT_JOIN_RULE s1 `s191:armstate`) THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC; DISCH_TAC]) THEN
  (SUBGOAL_THEN `!j. j < 1792 ==> abs(ival(mld_polyvec_map mld_poly_ntt (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. (skb:num->byte)(128 + j))) j)) < &94279689` ASSUME_TAC THENL
        [MP_TAC(SPECL [`7`; `mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. (skb:num->byte)(128 + j))`] MLD_LAZY_POLYVEC_NTT_BOUND) THEN
         CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
         DISCH_THEN MATCH_MP_TAC THEN
         REWRITE_TAC[mld_polyvec_unpack; mld_polyvec; MLD_LAZY_ETA_UNPACK_BOUND];
         ALL_TAC]) THEN
  (PK87_BYTES_SLICE_TAC `!j. j < 768 ==> read(memory :> bytes8(word_add sk (word(800 + j)))) s191 = (skb:num->byte)(800 + j)`) THEN
  (MP_TAC(ISPECL [(parse_term(Printf.sprintf "word_add (stackpointer:int64) (word %d)" rho)); `skb:num->byte`; `s191:armstate`] MLD_BYTES32_OF_CHUNKS) THEN ANTS_TAC THENL [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN ASM_REWRITE_TAC[]; REWRITE_TAC[GSYM mld_sk_rho] THEN DISCH_THEN(fun th -> FIRST_ASSUM(fun eq -> if concl eq = `mld_sk_rho skb = r` then ASSUME_TAC(REWRITE_RULE[eq] th) else NO_TAC))]) THEN
  (PK87_CALL_TAC "H_CPT"
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `mld_polyvec_map mld_poly_ntt (mld_polyvec_unpack 96 mld_polyeta_unpack_2 (\j. (skb:num->byte)(128 + j)))`;
    `\j. (skb:num->byte)(800 + j)`; `r:num`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 192) THEN
  (ARM_STEPS_TAC PK87_EXEC [193]) THEN
  (ARM_STEPS_TAC PK87_EXEC [194] THEN MLKEM_NATIVE_ADRP_TAC) THEN
  (ARM_STEPS_TAC PK87_EXEC (195--200)) THEN
  (ARM_STEPS_TAC PK87_EXEC [201] THEN MLKEM_NATIVE_ADRP_TAC) THEN
  (ARM_STEPS_TAC PK87_EXEC (202--203)) THEN
  (ARM_STEPS_TAC PK87_EXEC [204] THEN MLKEM_NATIVE_ADRP_TAC) THEN
  (ARM_STEPS_TAC PK87_EXEC (205--206)) THEN
  (ARM_STEPS_TAC PK87_EXEC [207] THEN MLKEM_NATIVE_ADRP_TAC) THEN
  (ARM_STEPS_TAC PK87_EXEC (208--211)) THEN
  (PK87_CHUNKS_TAC `sk:int64` 1568 `\j. (skb:num->byte) (1568 + j)` "s211") THEN
  (PK87_CHUNKS_TAC `stackpointer:int64` t0 PK87_T0F "s211") THEN
  (PK87_CALL_TAC "H_CMP" [`sk:int64`; `read X22 s`; `mld_chunk128 (\j. (skb:num->byte) (1568 + j))`; mk_comb(`mld_chunk128`,PK87_T0F); `pc:num`] 212) THEN
  (MAP_EVERY (fun r ->
  let q = mk_var("q"^r,`:int128`) in
  let rd = mk_comb(mk_comb(`read:(armstate,int128)component->armstate->int128`,mk_const("Q"^r,[])),`s212:armstate`) in
  SUBGOAL_THEN (mk_exists(q,mk_eq(rd,q))) STRIP_ASSUME_TAC THENL
   [EXISTS_TAC rd THEN REFL_TAC; ALL_TAC]) ["0";"1";"3";"4";"5";"6";"7";"16"]) THEN
  (ARM_STEPS_TAC PK87_EXEC (213--243)) THEN
  (PK87_PK_TAC "s243") THEN
  (PK87_ABBREV_REG_TAC "X9" "s243" "x9v") THEN
  (PK87_MASK_RULE "s243") THEN
  (PK87_CALL_TAC "H_SHAKE" [`read SP s`; `read X19 s`; PK87_PKNUM; `read X26 s`; `read X27 s`; `read X0 s`; `pc:num`] 244) THEN
  (PK87_TRC_TAC trc "s244") THEN
  (ARM_STEPS_TAC PK87_EXEC (245--297)) THEN
  (PK87_CHECK_TAC "s297") THEN
  (USE_THEN "CHECK" (fun th -> RULE_ASSUM_TAC(fun t -> if pfs_pcev t then REWRITE_RULE[th] t else t))) THEN
  (PFS_CASES_TAC PK87_VALID) THEN
  (PK87_RUN_TAC PK87_EXEC "mldsa87_pk_from_sk" "adrp6" PK87_ALLOWED 298) THEN
  PK87_FINAL_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together.                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_PK_FROM_SK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN PK87_CALLEES_TAC THEN
  CONCRETIZE_F_EVENTS_TAC PK87_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  PK87_SETUP_TAC THEN
  ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [REWRITE_TAC[ASSUME `aligned 32 (stackpointer:int64)`] THEN
    PK87_CASE_TAC 5344;
    REWRITE_TAC[ASSUME `~aligned 32 (stackpointer:int64)`] THEN
    PK87_CASE_TAC 5328]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_PK_FROM_SK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_PK_FROM_SK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_PK_FROM_SK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_PK_FROM_SK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_PK_FROM_SK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL)
        th)));;
