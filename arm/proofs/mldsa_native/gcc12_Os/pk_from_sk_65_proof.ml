(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The public key of a secret key: the proof (see pk_from_sk_65_spec.ml).    *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_Os/pk_from_sk_65_spec.ml";;
needs "arm/proofs/utils/mldsa_native_top.ml";;

let PS65_EXEC = MLDSA_NATIVE_PK_FROM_SK_65_GCC12_OS_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The parameters of the parameter set (k = 6, l = 5, eta = 4, 128 bytes for  *)
(* a packed polynomial of s1 and s2), for the terms and offsets of           *)
(* utils/mldsa_native_top.ml, with the stack (46960 bytes, 8976 of them for  *)
(* the function). The callee theorems of the record are not used.            *)
(* ------------------------------------------------------------------------- *)

let PS65_PRM =
 { pfs_exec = PS65_EXEC;
   pfs_fn = "mldsa65_pk_from_sk";
   pfs_k = 6; pfs_l = 5; pfs_eta = 4; pfs_p = 128;
   pfs_unpack = `mld_polyeta_unpack_4`;
   pfs_sk = 4032; pfs_pk = 1952; pfs_fr = 46960; pfs_own = 8976;
   pfs_cpt = TRUTH; pfs_unpack_th = TRUTH; pfs_chkl = TRUTH;
   pfs_chkk = TRUTH; pfs_ntt = TRUTH; pfs_shake = TRUTH;
   pfs_x28 = `word 0:int64`; pfs_cpt_pre = ALL_TAC };;

(* ------------------------------------------------------------------------- *)
(* Two arrays of bytes are equal as numbers if and only if they are equal    *)
(* byte by byte; and the bytes of a zeroed region.                           *)
(* ------------------------------------------------------------------------- *)

let MLD_NUM_BYTELIST_EQ = prove
 (`!(f:num->byte) g len.
        num_of_bytelist(list_of_seq f len) = num_of_bytelist(list_of_seq g len)
        <=> (!i. i < len ==> f i = g i)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `bytelist_of_num len`) THEN
    MP_TAC(ISPEC `list_of_seq (f:num->byte) len` BYTELIST_OF_NUM_OF_BYTELIST) THEN
    MP_TAC(ISPEC `list_of_seq (g:num->byte) len` BYTELIST_OF_NUM_OF_BYTELIST) THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN REPEAT DISCH_TAC THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `list_of_seq (f:num->byte) len = list_of_seq g len`
     MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `EL i:byte list->byte`) THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ];
    DISCH_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC LIST_OF_SEQ_EQ THEN
    ASM_SIMP_TAC[]]);;
let MLD_ZERO_BYTELIST = prove
 (`!n. num_of_bytelist(list_of_seq (\j:num. word 0:byte) n) = 0`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[list_of_seq; num_of_bytelist; LIST_OF_SEQ_ADD_GEN;
                  NUM_OF_BYTELIST_APPEND; LENGTH_LIST_OF_SEQ; ADD1] THEN
  REWRITE_TAC[num_of_bytelist; VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES]);;

let MLD_ZERO_BYTES8 = prove
 (`!(a:int64) n s.
        read (memory :> bytes(a,n)) s = 0
        ==> !j. j < n ==> read (memory :> bytes8(word_add a (word j))) s =
                          word 0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`a:int64`; `n:num`; `\j:num. word 0:byte`; `s:armstate`]
               BYTES8_OF_BYTES) THEN
  ASM_REWRITE_TAC[MLD_ZERO_BYTELIST] THEN SIMP_TAC[]);;

let MLD_CHUNK_SHIFT32 = prove
 (`!(f:num->byte) i.
        mld_chunk128 (\j. f(32 + j)) i = mld_chunk128 f (2 + i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_chunk128] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let MLD_BYTES64_OF_CHUNKS = prove
 (`!a:int64 (f:num->byte) s.
        read (memory :> bytes128 a) s = mld_chunk128 f 0 /\
        read (memory :> bytes128 (word_add a (word 16))) s = mld_chunk128 f 1 /\
        read (memory :> bytes128 (word_add a (word 32))) s = mld_chunk128 f 2 /\
        read (memory :> bytes128 (word_add a (word 48))) s = mld_chunk128 f 3
        ==> read (memory :> bytes(a,64)) s = num_of_bytelist(list_of_seq f 64)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `f:num->byte`; `s:armstate`] MLD_BYTES32_OF_CHUNKS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`word_add a (word 32):int64`; `\j. (f:num->byte)(32 + j)`;
                 `s:armstate`] MLD_BYTES32_OF_CHUNKS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MLD_CHUNK_SHIFT32] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `64 = 32 + 32`; LIST_OF_SEQ_ADD_GEN;
              NUM_OF_BYTELIST_APPEND; LENGTH_LIST_OF_SEQ] THEN
  REPEAT DISCH_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  ONCE_REWRITE_TAC[READ_BYTES_COMBINE] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The calls. The frame of the function is at stackpointer + 37984 (the      *)
(* frames of the callees are below it), with the buffers, aligned to 32      *)
(* bytes, at a base b that depends on whether the stack pointer is a         *)
(* multiple of 32 (pfs_offs of utils/mldsa_native_top.ml). The events before *)
(* a call are functions of the variables pfs_allowed.                        *)
(* ------------------------------------------------------------------------- *)

let PS65_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_Os_mc PS65_EXEC name ilist
   pfs_allowed n;;

let PS65_STEPS_TAC bth a b =
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC PS65_EXEC [n] THEN
    (if n = 15 then MEXP_BUFFER_TAC bth else ALL_TAC) THEN
    (if n = 9 then MLKEM_NATIVE_ADRP_TAC else ALL_TAC)) (a--b);;

(* ------------------------------------------------------------------------- *)
(* The start of the proof of FULL: the theorems for the callees, the events  *)
(* of the function as those before the test of the result (the prologue)     *)
(* followed by those after it, which are different if the key is valid and   *)
(* if not, and the frame, with one case for each alignment of the stack.     *)
(* ------------------------------------------------------------------------- *)

let PS65_SETUP_TAC =
  let template =
   `\(pk:int64) (sk:int64) (rho:num) (valid:bool) (guard:int64) (mf:int64)
     (pc:num) (stackpointer:int64) (returnaddress:int64).
     if aligned 32 stackpointer
     then (if valid
           then f_ev_av pk sk rho guard mf pc stackpointer returnaddress
           else f_ev_ai pk sk rho guard mf pc stackpointer returnaddress)
     else (if valid
           then f_ev_uv pk sk rho guard mf pc stackpointer returnaddress
           else f_ev_ui pk sk rho guard mf pc stackpointer returnaddress)
     :(uarch_event)list` in
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_GCC12_OS_IMAGE_SUBROUTINE_FULL
               th) "H_CPT" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MP (SPEC_ALL MLDSA_NATIVE_ZEROIZE_4_GCC12_OS_IMAGE_SUBROUTINE_FULL) th)
     "H_ZERO" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MP (SPEC_ALL MLDSA_NATIVE_SHAKE256_GCC12_OS_IMAGE_SUBROUTINE_FULL) th)
     "H_SHAKE") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_CT_MEMCMP_2_GCC12_OS_IMAGE_SUBROUTINE_FULL "H_CMP" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYVECL_UNPACK_ETA_65_GCC12_OS_IMAGE_SUBROUTINE_FULL
   "H_UNPACK" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYVECL_CHKNORM_65_GCC12_OS_IMAGE_SUBROUTINE_FULL
   "H_CHKL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_65_GCC12_OS_IMAGE_SUBROUTINE_FULL
   "H_CHKK" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYVECL_NTT_65_GCC12_OS_IMAGE_SUBROUTINE_FULL "H_NTT" THEN
  CONCRETIZE_F_EVENTS_TAC template THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  ABBREV_TAC `r = mld_sk_rho skb` THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst PS65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC (subst [pfs_sp PS65_PRM.pfs_fr,`a:int64`]
                   `aligned 16 (a:int64)`) THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
    SPECL [`pc:num`; `got_memset:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    let r = "X"^string_of_int n in
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (mk_const(r,[]))) (19--28);;

(* ------------------------------------------------------------------------- *)
(* The code before the call of mld_compute_pack_t0_t165: the copies of rho,  *)
(* the key and tr into the buffers (which the 128-bit chunks of the secret   *)
(* key give), the unpacking of s1, the checks of s1 and s2, the transform of *)
(* s1, and the copy of rho into the public key.                              *)
(* ------------------------------------------------------------------------- *)

let PS65_PREFIX_TAC b =
  let (s1,s2,skt0,t0,pkf,valid,m,h,chk1,chk2) = pfs_terms PS65_PRM in
  let (ca,cu) = pfs_bases PS65_PRM in
  let (t0b,s2k,trc,tr,key,rho) = pfs_offs PS65_PRM b in
  let bth = MEXP_BUFFER_ADDRESS_RULE (pfs_c PS65_PRM) ca cu in
  let st n = mk_var("s" ^ string_of_int n,`:armstate`) in
  let inst = pfs_inst PS65_PRM in
  let slice off len s =
    inst(subst [pfs_n off,`ofs:num`; pfs_n len,`n:num`; st s,`s:armstate`]
      `!j. j < n ==> read(memory :> bytes8(word_add sk (word(ofs + j)))) s =
                     (skb:num->byte)(ofs + j)`) in
  FULL_INIT_TAC THEN PFS_SK_CHUNKS_TAC PS65_PRM THEN
  PS65_STEPS_TAC bth 1 43 THEN
  VEC_SLICE_TAC (slice 128 640 43) THEN
  PS65_CALL_TAC "H_UNPACK"
   [`read X0 s`; `read X1 s`; `\j. (skb:num->byte)(128 + j)`; `pc:num`;
    `read SP s`; `read X30 s`] 44 THEN
  PS65_STEPS_TAC bth 45 47 THEN
  PS65_CALL_TAC "H_CHKL"
   [`read X0 s`; s1; `read X1 s`; `pc:num`; `read SP s`; `read X30 s`] 48 THEN
  PS65_STEPS_TAC bth 49 53 THEN
  VEC_SLICE_TAC (slice 768 768 53) THEN
  PS65_CALL_TAC "H_CHKK"
   [`read X0 s`; inst `\j. (skb:num->byte)(S2O + j)`; `read X1 s`;
    `read X2 s`; `pc:num`; `read SP s`; `read X30 s`] 54 THEN
  PS65_STEPS_TAC bth 55 57 THEN
  PS65_CALL_TAC "H_NTT"
   [`read X0 s`; s1; `pc:num`; `read SP s`; `read X30 s`] 58 THEN
  PS65_STEPS_TAC bth 59 66 THEN
  MP_TAC(ISPECL [pfs_sp rho; `skb:num->byte`; st 66]
                MLD_BYTES32_OF_CHUNKS) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM mld_sk_rho] THEN
    DISCH_THEN(fun th -> FIRST_ASSUM(fun eq ->
      if concl eq = `mld_sk_rho skb = r` then ASSUME_TAC(REWRITE_RULE[eq] th)
      else NO_TAC))] THEN
  PS65_CALL_TAC "H_CPT"
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    mk_comb(`mld_polyvec_map mld_poly_ntt`,s1);
    inst `\j. (skb:num->byte)(S2O + j)`; `r:num`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 67;;

let PS65_B1_TAC b =
  let (s1,s2,skt0,t0,pkf,valid,m,h,chk1,chk2) = pfs_terms PS65_PRM in
  let (t0b,s2k,trc,tr,key,rho) = pfs_offs PS65_PRM b in
  let (ca,cu) = pfs_bases PS65_PRM in
  let bth = MEXP_BUFFER_ADDRESS_RULE (pfs_c PS65_PRM) ca cu in
  let inst = pfs_inst PS65_PRM in
  let teq = (REWRITE_CONV[mld_pk_from_sk_t; mld_sk_s1] THENC
             REWRITE_CONV[ADD_ASSOC] THENC NUM_REDUCE_CONV)
            (inst `mld_pk_from_sk_t LL unpack PP (skb:num->byte)`) in
  let t0n = pfs_n 2496 in
  PS65_STEPS_TAC bth 68 75 THEN
  FIRST_ASSUM(fun th1 ->
    if lhs(concl th1) = `read (memory :> bytes128 pk) s75` then
      FIRST_ASSUM(fun th2 ->
        if lhs(concl th2) =
           `read (memory :> bytes128 (word_add pk (word 16))) s75`
        then ASSUME_TAC(MATCH_MP MLD_BYTES8_OF_CHUNKS2 (CONJ th1 th2))
        else NO_TAC)
    else NO_TAC) THEN
  FIRST_ASSUM(fun th1 ->
    if can (term_match [] `!j. j < 32 ==> read (memory :> bytes8
              (word_add pk (word j))) s75 = (skb:num->byte) j`) (concl th1)
    then FIRST_ASSUM(fun th2 ->
      if can (term_match [] `!j. j < 1920 ==> read (memory :> bytes8
                (word_add pk (word(32 + j)))) s75 = (g:num->byte) j`)
             (concl th2)
      then ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_ADD_CONV)
                       (MATCH_MP MLD_BYTES8_JOIN (CONJ th1 th2)))
      else NO_TAC)
    else NO_TAC) THEN
  SUBGOAL_THEN (subst [m,`m:num`] `read (memory :> bytes(pk,1952)) s75 = m`)
   ASSUME_TAC THENL
   [MATCH_MP_TAC READ_BYTES_OF_BYTES8 THEN X_GEN_TAC `j:num` THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
      can (term_match [] `!j. j < 1952 ==> read (memory :> bytes8
                (word_add pk (word j))) s75 = (if j < 32 then f j else g (j - 32))`)
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[mld_pk_from_sk_pk; teq] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC];;

let PS65_B2_TAC b =
  let (s1,s2,skt0,t0,pkf,valid,m,h,chk1,chk2) = pfs_terms PS65_PRM in
  let (t0b,s2k,trc,tr,key,rho) = pfs_offs PS65_PRM b in
  let inst = pfs_inst PS65_PRM in
  let teq = (REWRITE_CONV[mld_pk_from_sk_t; mld_sk_s1] THENC
             REWRITE_CONV[ADD_ASSOC] THENC NUM_REDUCE_CONV)
            (inst `mld_pk_from_sk_t LL unpack PP (skb:num->byte)`) in
  let nt0 = subst [t0,`f:num->byte`]
    `num_of_bytelist(list_of_seq f 2496)`
  and nsk = subst [skt0,`f:num->byte`]
    `num_of_bytelist(list_of_seq f 2496)` in
  SUBGOAL_THEN
   (subst [pfs_sp t0b,`a:int64`; nt0,`n:num`]
     `read (memory :> bytes(a,2496)) s75 = n`) ASSUME_TAC THENL
   [MATCH_MP_TAC READ_BYTES_OF_BYTES8 THEN X_GEN_TAC `jj:num` THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    REWRITE_TAC[teq] THEN
    FIRST_ASSUM(fun th ->
      if concl th = `mld_sk_rho skb = r` then REWRITE_TAC[th] else NO_TAC) THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [] `!j. j < 2496 ==> read (memory :> bytes8
          (word_add stackpointer (word(n + j)))) s75 = (f:num->byte) j`)
          (concl th)
      then ACCEPT_TAC(MP (SPEC `jj:num` th) (ASSUME `jj < 2496`))
      else NO_TAC);
    ALL_TAC] THEN
  SUBGOAL_THEN
   (subst [nsk,`n:num`] `read (memory :> bytes(word_add sk (word 1536),2496)) s75 = n`)
   ASSUME_TAC THENL
   [MATCH_MP_TAC READ_BYTES_OF_BYTES8 THEN X_GEN_TAC `jj:num` THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    BETA_TAC THEN
    FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN SIMPLE_ARITH_TAC);
    ALL_TAC] THEN
  PS65_CALL_TAC "H_CMP"
   [`read X0 s`; `read X1 s`; `2496`; nt0; nsk; `pc:num`; `read X30 s`] 76;;

(* ------------------------------------------------------------------------- *)
(* The hash of the public key, and the comparison of tr with it.             *)
(* ------------------------------------------------------------------------- *)

let PS65_C1_TAC b =
  let (s1,s2,skt0,t0,pkf,valid,m,h,chk1,chk2) = pfs_terms PS65_PRM in
  let (t0b,s2k,trc,tr,key,rho) = pfs_offs PS65_PRM b in
  let (ca,cu) = pfs_bases PS65_PRM in
  let bth = MEXP_BUFFER_ADDRESS_RULE (pfs_c PS65_PRM) ca cu in
  let g = `\j. (skb:num->byte)(64 + j)` in
  let ceq = CONJUNCTS(REWRITE_RULE[]
              (BETA_RULE(SPECL [`skb:num->byte`; g] MLD_CHUNKS4_EQ))) in
  let ntr = subst [g,`f:num->byte`] `num_of_bytelist(list_of_seq f 64)`
  and nh = subst [h,`f:num->byte`] `num_of_bytelist(list_of_seq f 64)` in
  PS65_STEPS_TAC bth 77 83 THEN
  PS65_CALL_TAC "H_SHAKE"
   [`read X0 s`; `64`; `read X2 s`; `1952`; m; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] 84 THEN
  PS65_STEPS_TAC bth 85 88 THEN
  SUBGOAL_THEN (subst [pfs_sp tr,`a:int64`; ntr,`n:num`]
                  `read (memory :> bytes(a,64)) s88 = n`) ASSUME_TAC THENL
   [MATCH_MP_TAC MLD_BYTES64_OF_CHUNKS THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC(map GSYM ceq);
    ALL_TAC] THEN
  PS65_CALL_TAC "H_CMP"
   [`read X0 s`; `read X1 s`; `64`; ntr; nh; `pc:num`; `read X30 s`] 89;;

(* ------------------------------------------------------------------------- *)
(* The test of the three checks: the branch is taken if and only if the key  *)
(* is valid (mld_pk_from_sk_valid), and the proof splits on it.              *)
(* ------------------------------------------------------------------------- *)

let PS65_C2_TAC b =
  let (s1,s2,skt0,t0,pkf,valid,m,h,chk1,chk2) = pfs_terms PS65_PRM in
  let (ca,cu) = pfs_bases PS65_PRM in
  let bth = MEXP_BUFFER_ADDRESS_RULE (pfs_c PS65_PRM) ca cu in
  let inst = pfs_inst PS65_PRM in
  let vth = (REWRITE_CONV[mld_pk_from_sk_valid; mld_sk_s1; mld_sk_s2] THENC
             REWRITE_CONV[ADD_ASSOC] THENC NUM_REDUCE_CONV) valid in
  let n1 = subst [t0,`f:num->byte`] `num_of_bytelist(list_of_seq f 2496)`
  and m1 = subst [skt0,`f:num->byte`] `num_of_bytelist(list_of_seq f 2496)`
  and n2 = subst [`\j. (skb:num->byte)(64 + j)`,`f:num->byte`]
             `num_of_bytelist(list_of_seq f 64)`
  and m2 = subst [h,`f:num->byte`] `num_of_bytelist(list_of_seq f 64)` in
  PS65_STEPS_TAC bth 90 96 THEN
  W(fun g ->
    let pcv = pfs_asm_rhs g `read PC s96` in
    let cond = rand(rator(rator pcv)) in
    let t0eq = mk_iff(inst(subst [t0,`t0c:num->byte`; skt0,`skt0:num->byte`]
        `mld_ct_memcmp t0c skt0 T0N = word 0`), mk_eq(n1,m1))
    and treq = mk_iff(mk_eq(list_mk_comb(`mld_ct_memcmp`,
           [`\j. (skb:num->byte)(64 + j)`; h; `64`]), `word 0:byte`),
         mk_eq(n2,m2)) in
    SUBGOAL_THEN t0eq (LABEL_TAC "T0EQ") THENL
     [REWRITE_TAC[MLD_CT_MEMCMP_EQ_0; MLD_NUM_BYTELIST_EQ] THEN
      BETA_TAC THEN REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN treq (LABEL_TAC "TREQ") THENL
     [REWRITE_TAC[MLD_CT_MEMCMP_EQ_0; MLD_NUM_BYTELIST_EQ] THEN
      BETA_TAC THEN REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN (mk_iff(cond, valid)) (LABEL_TAC "CHECK") THENL
     [USE_THEN "T0EQ" (fun t0th -> USE_THEN "TREQ" (fun trth ->
        REWRITE_TAC[vth; t0th; trth])) THEN
      SPEC_TAC(mk_eq(n1,m1),`a:bool`) THEN SPEC_TAC(mk_eq(n2,m2),`b:bool`) THEN
      SPEC_TAC(chk2,`c2:int32`) THEN SPEC_TAC(chk1,`c1:int32`) THEN
      REPEAT GEN_TAC THEN BOOL_CASES_TAC `a:bool` THEN
      BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[] THEN
      SPEC_TAC(`c2:int32`,`c2:int32`) THEN SPEC_TAC(`c1:int32`,`c1:int32`)
      THEN W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w));
      ALL_TAC] THEN
    USE_THEN "CHECK" (fun th -> RULE_ASSUM_TAC(fun t ->
      if pfs_pcev t then REWRITE_RULE[th] t else t))) THEN
  PFS_CASES_TAC valid;;

(* ------------------------------------------------------------------------- *)
(* The two paths to the return, with the zeroing of the buffers (and of the  *)
(* public key if the key is not valid), the check of the canary and the      *)
(* postcondition.                                                            *)
(* ------------------------------------------------------------------------- *)

let PS65_ZERO_TAC n len =
  PS65_CALL_TAC "H_ZERO"
   [`read X0 s`; mk_small_numeral len; `pc:num`; `read SP s`;
    `read X30 s`] n;;

let PS65_VALID_TAC =
  let (s1,s2,skt0,t0,pkf,valid,m,h,chk1,chk2) = pfs_terms PS65_PRM in
  ARM_STEPS_TAC PS65_EXEC (97--99) THEN PS65_ZERO_TAC 100 2496 THEN
  ARM_STEPS_TAC PS65_EXEC (101--103) THEN PS65_ZERO_TAC 104 1024 THEN
  ARM_STEPS_TAC PS65_EXEC (105--107) THEN PS65_ZERO_TAC 108 5120 THEN
  ARM_STEPS_TAC PS65_EXEC (109--112) THEN PS65_ZERO_TAC 113 32 THEN
  ARM_STEPS_TAC PS65_EXEC (114--116) THEN PS65_ZERO_TAC 117 64 THEN
  ARM_STEPS_TAC PS65_EXEC (118--120) THEN PS65_ZERO_TAC 121 64 THEN
  ARM_STEPS_TAC PS65_EXEC (122--124) THEN PS65_ZERO_TAC 125 32 THEN
  ARM_STEPS_TAC PS65_EXEC (126--126) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC PS65_EXEC (127--142) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes(pk,1952)) s = n`) (concl th)
    then ASSUME_TAC(MATCH_MP BYTES8_OF_BYTES th) else NO_TAC) THEN
  PFS_FINAL_TAC;;

let PS65_INVALID_TAC =
  ARM_STEPS_TAC PS65_EXEC (97--100) THEN PS65_ZERO_TAC 101 1952 THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes(pk,1952)) s = 0`) (concl th)
    then ASSUME_TAC(MATCH_MP MLD_ZERO_BYTES8 th) else NO_TAC) THEN
  ARM_STEPS_TAC PS65_EXEC (102--104) THEN PS65_ZERO_TAC 105 2496 THEN
  ARM_STEPS_TAC PS65_EXEC (106--108) THEN PS65_ZERO_TAC 109 1024 THEN
  ARM_STEPS_TAC PS65_EXEC (110--112) THEN PS65_ZERO_TAC 113 5120 THEN
  ARM_STEPS_TAC PS65_EXEC (114--117) THEN PS65_ZERO_TAC 118 32 THEN
  ARM_STEPS_TAC PS65_EXEC (119--121) THEN PS65_ZERO_TAC 122 64 THEN
  ARM_STEPS_TAC PS65_EXEC (123--125) THEN PS65_ZERO_TAC 126 64 THEN
  ARM_STEPS_TAC PS65_EXEC (127--129) THEN PS65_ZERO_TAC 130 32 THEN
  ARM_STEPS_TAC PS65_EXEC (131--131) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC PS65_EXEC (132--147) THEN
  PFS_FINAL_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together, with a case for    *)
(* each alignment of the stack pointer, and in each the cases of the check.  *)
(* ------------------------------------------------------------------------- *)

let PS65_CASE_TAC b =
  PS65_PREFIX_TAC b THEN PS65_B1_TAC b THEN PS65_B2_TAC b THEN
  PS65_C1_TAC b THEN PS65_C2_TAC b THENL
   [PS65_VALID_TAC; PS65_INVALID_TAC];;

let MLDSA_NATIVE_PK_FROM_SK_65_GCC12_OS_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_PK_FROM_SK_65_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  PS65_SETUP_TAC THEN
  PAR_THENL (ASM_CASES_TAC `aligned 32 (stackpointer:int64)`)
   [REWRITE_TAC[ASSUME `aligned 32 (stackpointer:int64)`] THEN
    PS65_CASE_TAC 38112;
    REWRITE_TAC[ASSUME `~aligned 32 (stackpointer:int64)`] THEN
    PS65_CASE_TAC 38096]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_PK_FROM_SK_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_PK_FROM_SK_65_GCC12_OS_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_PK_FROM_SK_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_PK_FROM_SK_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_PK_FROM_SK_65_GCC12_OS_IMAGE_SUBROUTINE_FULL)
        th)));;
