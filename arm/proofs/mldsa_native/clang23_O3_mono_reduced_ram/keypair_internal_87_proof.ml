(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Key generation: the proof (see keypair_internal_87_spec.ml). As for      *)
(* mldsa44 (keypair_internal_44_proof.ml): clang has inlined the SHAKE256 of *)
(* the seed, the packing of s1 and s2 and the SHAKE256 of the public key,    *)
(* and the proof composes the theorems for the callees and the lemmas for    *)
(* those parts (inline_keypair_87.ml) in the order of the code, with the     *)
(* frame at fp = stackpointer + b (b = 5344 or 5328): the polynomials at     *)
(* fp + 352 (s2 sampled first, then s1; s1 in fp + 352 + 1024 k for k < 7), *)
(* the seed buffer at fp + 7648, the state of SHAKE256 at fp + 7776, tr at   *)
(* fp + 7520 and the canary at fp + 7992.                                    *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/keypair_internal_87_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_ntt_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/lazy_eq_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_probe.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_keypair_87.ml";;
needs "arm/proofs/utils/mldsa_native_verify.ml";;
needs "arm/proofs/utils/mldsa_native_top.ml";;
needs "arm/proofs/utils/mldsa_native_wrap.ml";;
needs "arm/proofs/utils/mldsa_native_keypair.ml";;

let KI87_EXEC = MLDSA_NATIVE_KEYPAIR_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;
let KI87_MC = mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc;;

let KI87_ALLOWED =
  [`pk:int64`; `sk:int64`; `seed:int64`; `rhov:num`; `D:num->bool list`;
   `guard:int64`; `mf:int64`; `mc:int64`; `pc:num`; `stackpointer:int64`;
   `returnaddress:int64`];;

let KI87_CALL_TAC name ilist n =
  FULL_CALL_TAC KI87_MC KI87_EXEC name ilist KI87_ALLOWED n;;

let KI87_N n = mk_small_numeral n;;

let KI87_SP n =
  mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
          mk_comb(`word:num->int64`,KI87_N n));;

let KI87_ST n = mk_var("s"^string_of_int n,`:armstate`);;

let KI87_POLY n =
  mk_comb(`mld_poly_uniform_eta 2 (mld_keypair_rhoprime 8 7 SEED)`,
          mk_comb(`word:num->byte`,KI87_N n));;

(* ------------------------------------------------------------------------- *)
(* The callees and the inlined regions, as "H_..." assumptions.              *)
(* ------------------------------------------------------------------------- *)

let KI87_CALLEES_TAC =
  FIRST_ASSUM(fun th ->
    let m1 = CONJUNCT1 th in
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] m1)
     "H_MEMSET" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP
       MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL th)
     "H_CPT" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP
       MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL m1)
     "H_ETA") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
   "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC KI87_SEED "H_SEED" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC KI87_SHAKE "H_SHAKE" THEN
  MAP_EVERY (fun (th,k) ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC th ("H_P"^string_of_int k))
   (zip KI87_PACK_THS (0--14));;

(* ------------------------------------------------------------------------- *)
(* For each nonce n of the samplings: the termination of its sampling and    *)
(* its declassified values D n in the form of the callee, with the nonce as  *)
(* val(word_zx(word n)) or val(word n) (as in the gcc proof).                *)
(* ------------------------------------------------------------------------- *)

let KI87_USED = `\n. n < 15 \/ n = 255`;;

let KI87_NONCE_TAC =
  FIRST_ASSUM(fun th ->
    if concl th <> `mld_keypair_terminates_87 SEED` then NO_TAC else
    let tth = REWRITE_RULE[mld_keypair_terminates_87] th in
    MAP_EVERY (fun n ->
      let nt = KI87_N n in
      let uth = prove(mk_comb(KI87_USED,nt), BETA_TAC THEN ARITH_TAC) in
      let ith = SPECL [`2`; `8`; `7`; KI87_USED; `SEED:num`; nt] in
      let th1 = MP (ith MLD_KEYPAIR_TERMINATES_USED) (CONJ tth uth) in
      let th2 = REWRITE_RULE[GSYM mld_keypair_declass_87]
                 (MP (ith MLD_KEYPAIR_DECLASS_USED) uth) in
      ASSUME_TAC th1 THEN
      FIRST_ASSUM(fun dth ->
        if concl dth = `mld_keypair_declass_87 SEED = D`
        then ASSUME_TAC(REWRITE_RULE[dth] th2) else NO_TAC) THEN
      ASSUME_TAC(WORD_REDUCE_CONV
        (mk_comb(`val:byte->num`,mk_comb(`word:num->byte`,nt)))) THEN
      (if n < 255 then
         ASSUME_TAC(WORD_REDUCE_CONV
           (mk_comb(`word_zx:int64->byte`,mk_comb(`word:num->int64`,nt))))
       else ALL_TAC)) [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;255]);;

(* ------------------------------------------------------------------------- *)
(* Facts about the buffers.                                                  *)
(* ------------------------------------------------------------------------- *)

let KI87_DROP_TAC pats =
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    exists (fun p -> can (term_match [] p) (concl th)) pats)));;

(*** The seed buffer from the output of SHAKE256 (with rho as rhov) ***)

let KI87_SEEDBUF_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes(a,128)) s =
          num_of_bytelist(list_of_seq (mld_shake256_byte 34 x) 128)`)
         (concl th)
    then W(fun (asl,w) ->
           let ath = snd(find (fun (_,a) ->
                       concl a = `mld_keypair_rho 8 7 SEED = rhov`) asl) in
           STRIP_ASSUME_TAC
            (REWRITE_RULE[ath]
              (CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                         NUM_REDUCE_CONV)
                (MATCH_MP MLD_KEYPAIR_SEEDBUF th))))
    else NO_TAC);;

(*** The 16-byte chunks of n bytes f at base + off ***)

let KI87_CHUNKS_TAC base off n fn sname =
  let sp = mk_var(sname,`:armstate`) in
  let offt = mk_small_numeral off in
  let b0 = mk_comb(mk_comb(`word_add:int64->int64->int64`,base),
                   mk_comb(`word:num->int64`,offt)) in
  SUBGOAL_THEN
   (subst [base,`BASE:int64`; offt,`OFF:num`; fn,`FN:num->byte`; sp,`s:armstate`;
           mk_small_numeral(n / 16),`K:num`]
     `!k. k < K ==> read (memory :> bytes128 (word_add (BASE:int64) (word (OFF + 16 * k)))) s =
                    mld_chunk128 (FN:num->byte) k`)
   (fun th -> MAP_EVERY (fun k ->
       ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)
         (MP (SPEC (mk_small_numeral k) th)
             (EQT_ELIM(NUM_REDUCE_CONV(mk_binary "<" (mk_small_numeral k,mk_small_numeral(n / 16))))))))
       (0--(n / 16 - 1))) THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [b0; mk_small_numeral n; fn; sp; `k:num`] BYTES128_OF_BYTES8) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
        REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN BETA_TAC THEN
        FIRST_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC;
        ASM_ARITH_TAC];
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      DISCH_THEN ACCEPT_TAC];
    ALL_TAC];;

(*** The 32 or 64 bytes at base + off from two or four chunks ***)

let KI_BYTES8_OF_CHUNKS4 = prove
 (`!(a:int64) (f:num->byte) s.
     read (memory :> bytes128 a) s = mld_chunk128 f 0 /\
     read (memory :> bytes128 (word_add a (word 16))) s = mld_chunk128 f 1 /\
     read (memory :> bytes128 (word_add a (word 32))) s = mld_chunk128 f 2 /\
     read (memory :> bytes128 (word_add a (word 48))) s = mld_chunk128 f 3
     ==> !j. j < 64 ==> read(memory :> bytes8(word_add a (word j))) s = f j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `f:num->byte`; `s:armstate`] MLD_BYTES8_OF_CHUNKS2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`word_add a (word 32):int64`; `\j. (f:num->byte) (32 + j)`;
                `s:armstate`] MLD_BYTES8_OF_CHUNKS2) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    SUBGOAL_THEN `mld_chunk128 (\j. (f:num->byte) (32 + j)) 0 = mld_chunk128 f 2 /\
                  mld_chunk128 (\j. (f:num->byte) (32 + j)) 1 = mld_chunk128 f 3`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
    REWRITE_TAC[mld_chunk128] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES; ADD_ASSOC] THEN
    CONV_TAC NUM_REDUCE_CONV;
    DISCH_TAC] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_CASES_TAC `j < 32` THEN
  ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j - 32`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(j < 32) ==> 32 + j - 32 = j`]);;

let KI87_BYTESN_TAC base off n fn sname =
  let sv = mk_var(sname,`:armstate`) in
  let a = if off = 0 then base else
          mk_comb(mk_comb(`word_add:int64->int64->int64`,base),
                  mk_comb(`word:num->int64`,mk_small_numeral off)) in
  let lem = if n = 32 then MLD_BYTES8_OF_CHUNKS2 else KI_BYTES8_OF_CHUNKS4 in
  let th0 = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                      DEPTH_CONV NUM_ADD_CONV)
              (SPECL [a; fn; sv] lem) in
  let hyps = conjuncts(lhand(concl th0)) in
  W(fun (asl,w) ->
    let ths = map (fun h -> snd(find (fun (_,th) -> concl th = h) asl)) hyps in
    let th1 = MP th0 (end_itlist CONJ ths) in
    ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                         DEPTH_CONV BETA_CONV) th1));;

(* ------------------------------------------------------------------------- *)
(* The vector s in the secret key after the eight packings, and s1 (in the   *)
(* NTT domain) from its four polynomials.                                    *)
(* ------------------------------------------------------------------------- *)

let KI87_SREGION n =
  subst [KI87_ST n,`s:armstate`]
   `!j. j < 1440
        ==> read (memory :> bytes8 (word_add sk (word (128 + j)))) s =
            mld_polyvec_pack 96 mld_polyeta_pack_2 (mld_keypair_s 2 8 7 SEED)
             j`;;

let KI87_S1 = `mld_keypair_s 2 8 7 SEED`;;

(*** The seven polynomials of s1 after the NTT as the vector ***)

let KI87_NTT_JOIN_TAC off sname =
  let sv = mk_var(sname,`:armstate`) in
  SUBGOAL_THEN
   (subst [mk_small_numeral off,`S1:num`; sv,`s:armstate`]
     `!i. i < 1792
          ==> read (memory :> bytes32 (word_add stackpointer (word (S1 + 4 * i)))) s =
              mld_polyvec_map mld_poly_ntt (mld_keypair_s 2 8 7 SEED) i`)
   ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1792 = 256 * 7`] THEN
    MATCH_MP_TAC MLD_KEYPAIR_JOIN32 THEN
    SIMP_TAC[MLD_POLYVEC_MAP_COEFF] THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC];;

(*** Polynomial p of s1 (sampled with the nonce p) as mld_poly_of of s1 ***)

let KI87_S1_SLICE_TAC off p sname =
  let sv = mk_var(sname,`:armstate`) in
  let pt = mk_small_numeral p in
  SUBGOAL_THEN
   (subst [mk_small_numeral off,`off:num`; pt,`p:num`; sv,`s:armstate`]
     `!j. j < 256 ==> read (memory :> bytes32 (word_add stackpointer (word (off + 4 * j)))) s =
          mld_poly_of (mld_keypair_s 2 8 7 SEED) p j`)
   ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[mld_keypair_s; MLD_POLY_OF_POLYVEC] THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] (subst [mk_small_numeral off,`off:num`; sv,`s:armstate`;
             mk_comb(`word:num->byte`,pt),`w:byte`]
        `!i. i < 256 ==> read (memory :> bytes32 (word_add stackpointer (word (off + 4 * i)))) s =
             mld_poly_uniform_eta 2 (mld_keypair_rhoprime 8 7 SEED) w i`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The setup: hypotheses, the addresses of the GOT, the canary, and the      *)
(* callee-saved registers (X19 to X29 and D8 to D15).                        *)
(* ------------------------------------------------------------------------- *)

let KI87_SETUP_TAC =
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst KI87_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 13504):int64)` THEN
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
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (mk_const("X"^string_of_int n,[]))) (19--29) THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_DREG_TAC ("d"^string_of_int n^"_init")
     (mk_const("D"^string_of_int n,[]))) (8--15);;

(*** The frame fp is 32-aligned in both cases ***)

let KI87_FP_ALIGNED = prove
 (`!sptr:int64. aligned 16 sptr
      ==> aligned 32 (word_add sptr (word(if aligned 32 sptr then 5344 else 5328)))`,
  REWRITE_TAC[MLD_WRAP_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let KI87_FP_ALIGNED_TAC =
  FIRST_ASSUM(fun a16 ->
    if concl a16 <> `aligned 16 (stackpointer:int64)` then NO_TAC else
    let th = MP (SPEC `stackpointer:int64` KI87_FP_ALIGNED) a16 in
    FIRST_ASSUM(fun cth ->
      if concl cth = `aligned 32 (stackpointer:int64)` ||
         concl cth = `~aligned 32 (stackpointer:int64)`
      then ASSUME_TAC(REWRITE_RULE[cth] th)
      else NO_TAC));;

let KI87_BUF_TAC =
  FIRST_ASSUM(fun a16 ->
    if concl a16 <> `aligned 16 (stackpointer:int64)` then NO_TAC else
    let th = MP (SPEC `stackpointer:int64` (MLD_WRAP_BUFFER_RULE `5344`)) a16 in
    FIRST_ASSUM(fun cth ->
      if concl cth = `aligned 32 (stackpointer:int64)` ||
         concl cth = `~aligned 32 (stackpointer:int64)`
      then RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_RULE[cth] th])
      else NO_TAC));;

(*** The 32 bytes of the key (seed buffer + 96) at fp + 7744 ***)

let KI87_KEY_TAC b sname =
  let sv = mk_var(sname,`:armstate`) in
  SUBGOAL_THEN
   (subst [mk_small_numeral(b + 7744),`K:num`; sv,`s:armstate`]
     `!j. j < 32 ==> read (memory :> bytes8 (word_add stackpointer (word (K + j)))) s =
                     mld_keypair_seedbuf 8 7 SEED (96 + j)`)
   ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `96 + j` o check (fun th ->
      can (term_match [] (subst [mk_small_numeral(b + 7648),`K:num`; sv,`s:armstate`]
        `!j. j < 128 ==> read (memory :> bytes8 (word_add stackpointer (word (K + j)))) s =
                         mld_keypair_seedbuf 8 7 SEED j`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE (subst [mk_small_numeral(b + 7648),`K:num`;
                                   mk_small_numeral(b + 7744),`L:num`]
                 `K + 96 + j = L + j`)];
    ALL_TAC];;

(*** Step to the return, with the call of memset through the PLT ***)

let rec KI87_RUN_TAC execth fn adrplab allowed n (asl,w) =
  let off = pfs_pc_offset (pfs_current_pc (asl,w)) in
  if off < 0 then ALL_TAC (asl,w)
  else if off = layout "plt_memset" then
    (LIBC_PLT_TAC execth (n - 1) THEN
     PFS_LIBC_SAFE_CALL_TAC "H_MEMSET" execth
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
       `read X30 s`] (ref allowed) (n + 4) THEN
     KI87_RUN_TAC execth fn adrplab allowed (n + 5)) (asl,w)
  else
    (ARM_STEPS_TAC execth [n] THEN
     (if off = layout(fn ^ "_" ^ adrplab) then MLKEM_NATIVE_ADRP_TAC
      else ALL_TAC) THEN
     PFS_DECIDE_TAC THEN KI87_RUN_TAC execth fn adrplab allowed (n + 1)) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* The parts of the simulation, in each case of the stack alignment, with    *)
(* the frame at fp = stackpointer + b.                                       *)
(* ------------------------------------------------------------------------- *)

(*** The prologue with the probe of the stack, and the SHAKE256 of the seed ***)

let KI87_PART1_TAC b =
  KGP_SP_BOUNDS_TAC 13504 THEN KI87_NONCE_TAC THEN FULL_INIT_TAC THEN
  KI87_FP_ALIGNED_TAC THEN
  ARM_STEPS_TAC KI87_EXEC (1--14) THEN KI87_BUF_TAC THEN
  MAP_EVERY (fun n -> KGP_PROBE_TAC 13504 KI87_EXEC n) (15--21) THEN
  ARM_STEPS_TAC KI87_EXEC [22] THEN
  KI87_CALL_TAC "H_SEED"
   [`read SP s`; `pk:int64`; `sk:int64`; `seed:int64`; `SEED:num`;
    `guard:int64`; `canary:int64`; `pc:num`] 23 THEN
  KI87_SEEDBUF_TAC;;

(*** A call of poly_uniform_eta_4x with the nonces n0 to n3 (after the bl ***)
(*** at step n - 1), then the four packings at steps n + 1 to n + 4       ***)

let KI87_ETA_TAC n n0 n1 n2 n3 =
  KI87_CALL_TAC "H_ETA"
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `mld_keypair_rhoprime 8 7 SEED`;
    mk_comb(`word:num->int64`,KI87_N n0);
    mk_comb(`word:num->int64`,KI87_N n1);
    mk_comb(`word:num->int64`,KI87_N n2);
    mk_comb(`word:num->byte`,KI87_N n3);
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] n;;

(*** The input of a packing at fp + off in the form b + off + 4 * i that ***)
(*** the precondition of the lemma takes, from the fact at b + off       ***)

let KI87_IN_TAC b off nonce sname =
  let sv = mk_var(sname,`:armstate`) in
  let tm = subst [mk_small_numeral b,`b:num`; mk_small_numeral off,`off:num`;
                  mk_small_numeral(b + off),`bo:num`; sv,`s:armstate`;
                  KI87_POLY nonce,`x:num->int32`]
   `!i. i < 256 ==> read (memory :> bytes32 (word_add stackpointer (word (b + off + 4 * i)))) s =
                    (x:num->int32) i` in
  let src = subst [mk_small_numeral(b + off),`bo:num`; sv,`s:armstate`;
                   KI87_POLY nonce,`x:num->int32`]
   `!i. i < 256 ==> read (memory :> bytes32 (word_add stackpointer (word (bo + 4 * i)))) s =
                    (x:num->int32) i` in
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if concl th = src then
      REWRITE_TAC[ARITH_RULE(subst [mk_small_numeral b,`b:num`; mk_small_numeral off,`off:num`;
                                    mk_small_numeral(b + off),`bo:num`]
                   `!i. b + off + 4 * i = bo + 4 * i`)] THEN ACCEPT_TAC th
      else NO_TAC);
    ALL_TAC];;

let KI87_PACK_TAC b k nonce n =
  let (inofs,_,_,_,_,_,_,_) = KP87_PACK_PARAMS k in
  KI87_IN_TAC b inofs nonce ("s"^string_of_int(n - 1)) THEN
  KI87_CALL_TAC ("H_P"^string_of_int k)
   [`read X19 s`; `read SP s`; KI87_POLY nonce; `pc:num`] n;;

let KI87_PART2_TAC b =
  ARM_STEPS_TAC KI87_EXEC [24] THEN
  KI87_ETA_TAC 25 11 12 13 14 THEN
  KI87_PACK_TAC b 0 11 26 THEN KI87_PACK_TAC b 1 12 27 THEN
  KI87_PACK_TAC b 2 13 28 THEN KI87_PACK_TAC b 3 14 29 THEN
  ARM_STEPS_TAC KI87_EXEC (30--43) THEN
  KI87_ETA_TAC 44 7 8 9 10 THEN
  KI87_PACK_TAC b 4 7 45 THEN KI87_PACK_TAC b 5 8 46 THEN
  KI87_PACK_TAC b 6 9 47 THEN KI87_PACK_TAC b 7 10 48 THEN
  ARM_STEPS_TAC KI87_EXEC (49--65) THEN
  KI87_ETA_TAC 66 4 5 6 255 THEN
  KI87_PACK_TAC b 8 4 67 THEN KI87_PACK_TAC b 9 5 68 THEN
  KI87_PACK_TAC b 10 6 69 THEN
  ARM_STEPS_TAC KI87_EXEC (70--83) THEN
  KI87_ETA_TAC 84 0 1 2 3 THEN
  KI87_PACK_TAC b 11 0 85 THEN KI87_PACK_TAC b 12 1 86 THEN
  KI87_PACK_TAC b 13 2 87 THEN KI87_PACK_TAC b 14 3 88 THEN
  SUBGOAL_THEN (KI87_SREGION 88) ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1440 = 96 * 15`] THEN
    MATCH_MP_TAC MLD_KEYPAIR_JOIN8 THEN SIMP_TAC[MLD_KEYPAIR_S_PACK_2] THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  KI87_DROP_TAC
   [`!j. j < 96
         ==> read (memory :> bytes8 (word_add sk (word (n + j)))) s =
             mld_polyeta_pack_2 x j`];;

(*** The NTT of s1, the copy of rho into pk and the computation of t ***)

let KI87_NTT_TAC b p n =
  KI87_S1_SLICE_TAC (b + 352 + 1024 * p) p ("s"^string_of_int(n - 1)) THEN
  KI87_CALL_TAC "H_NTT"
   [`read X0 s`;
    mk_comb(mk_comb(`mld_poly_of:(num->int32)->num->num->int32`,KI87_S1),
            mk_small_numeral p);
    `pc:num`; `read SP s`; `read X30 s`] n;;

let KI87_PART3_TAC b =
  ARM_STEPS_TAC KI87_EXEC (89--93) THEN KI87_NTT_TAC b 0 94 THEN
  ARM_STEPS_TAC KI87_EXEC (95--96) THEN KI87_NTT_TAC b 1 97 THEN
  ARM_STEPS_TAC KI87_EXEC (98--99) THEN KI87_NTT_TAC b 2 100 THEN
  ARM_STEPS_TAC KI87_EXEC (101--102) THEN KI87_NTT_TAC b 3 103 THEN
  ARM_STEPS_TAC KI87_EXEC (104--105) THEN KI87_NTT_TAC b 4 106 THEN
  ARM_STEPS_TAC KI87_EXEC (107--108) THEN KI87_NTT_TAC b 5 109 THEN
  ARM_STEPS_TAC KI87_EXEC (110--112) THEN KI87_NTT_TAC b 6 113 THEN
  KI87_CHUNKS_TAC `stackpointer:int64` (b + 7648) 32
   `mld_keypair_seedbuf 8 7 SEED` "s113" THEN
  ARM_STEPS_TAC KI87_EXEC (114--125) THEN
  KI87_NTT_JOIN_TAC (b + 352) "s125" THEN
  SUBGOAL_THEN
   `!j. j < 768
        ==> read (memory :> bytes8 (word_add sk (word (800 + j)))) s125 =
            mld_polyvec_pack 96 mld_polyeta_pack_2 (mld_keypair_s 2 8 7 SEED)
             (7 * 96 + j)`
   ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `7 * 96 + j` o check (fun th ->
      can (term_match [] (KI87_SREGION 125)) (concl th))) THEN
    REWRITE_TAC[ARITH_RULE `128 + 7 * 96 + j = 800 + j`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j < 1792
        ==> abs(ival(mld_polyvec_map mld_poly_ntt (mld_keypair_s 2 8 7 SEED) j)) <
            &94279689`
   ASSUME_TAC THENL
   [MP_TAC(SPECL [`7`; `mld_keypair_s 2 8 7 SEED`] MLD_LAZY_POLYVEC_NTT_BOUND) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(SPECL [`2`; `8`; `7`; `\n. n < 15 \/ n = 255`; `SEED:num`]
                 MLD_LAZY_KEYPAIR_S_BOUND) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[GSYM mld_keypair_terminates_87] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  KI87_CALL_TAC "H_CPT"
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `mld_polyvec_map mld_poly_ntt (mld_keypair_s 2 8 7 SEED)`;
    `\j. mld_polyvec_pack 96 mld_polyeta_pack_2 (mld_keypair_s 2 8 7 SEED)
          (7 * 96 + j)`;
    `rhov:num`; `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 126;;

(*** The public key, as mld_keypair_pk_87 byte by byte and as a number, ***)
(*** and tr = H(pk, 64)                                                  ***)

let KI87_PKNUM = `num_of_bytelist (list_of_seq (mld_keypair_pk_87 SEED) 2592)`;;

let KI87_PART4_TAC =
  SUBGOAL_THEN
   `mld_compute_t 7 mld_polyeta_unpack_2 96 rhov
     (mld_polyvec_map mld_poly_ntt (mld_keypair_s 2 8 7 SEED))
     (\j. mld_polyvec_pack 96 mld_polyeta_pack_2 (mld_keypair_s 2 8 7 SEED)
           (7 * 96 + j)) =
    mld_keypair_t 2 8 7 mld_polyeta_pack_2 mld_polyeta_unpack_2 96 SEED`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[mld_keypair_t] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  KI87_BYTESN_TAC `pk:int64` 0 32 `mld_keypair_seedbuf 8 7 SEED` "s126" THEN
  SUBGOAL_THEN
   `read (memory :> bytes(pk,32)) s126 = mld_keypair_rho 8 7 SEED`
   ASSUME_TAC THENL
   [REWRITE_TAC[mld_keypair_rho] THEN MATCH_MP_TAC READ_BYTES_OF_BYTES8 THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV
   (SPECL [`pk:int64`; `s126:armstate`; `2`; `8`; `7`; `mld_polyeta_pack_2`;
           `mld_polyeta_unpack_2`; `96`; `SEED:num`]
          MLD_KEYPAIR_PK_BYTES)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM mld_keypair_pk_87] THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `!j. j < 2592
              ==> read (memory :> bytes8 (word_add pk (word j))) s =
                  mld_keypair_pk_87 SEED j`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[ETA_AX]
          (REWRITE_RULE[GSYM MLD_KEYPAIR_BYTES_EQ_BYTES8] th))
    else NO_TAC) THEN
  KI87_CALL_TAC "H_SHAKE"
   [`read SP s`; `read X20 s`; KI87_PKNUM; `read X21 s`; `pc:num`] 127;;

(*** The rest of the secret key, the zeroing and the return ***)

(*** The saved D registers: zero extensions of 64-bit values to 128 bits ***)

let KI87_ZX_ZX = WORD_BLAST `word_zx (word_zx (x:int64):int128):int64 = x`;;

let KI87_TR = `mld_shake256_byte 2592 (num_of_bytelist (list_of_seq (mld_keypair_pk_87 SEED) 2592))`;;

let KI87_PART5_TAC b =
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes (a,64)) s =
          num_of_bytelist (list_of_seq (mld_shake256_byte 2592 x) 64)`) (concl th)
    then ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                     (MATCH_MP BYTES8_OF_BYTES th))
    else NO_TAC) THEN
  KI87_CHUNKS_TAC `stackpointer:int64` (b + 7520) 64 KI87_TR "s127" THEN
  KI87_KEY_TAC b "s127" THEN
  KI87_CHUNKS_TAC `stackpointer:int64` (b + 7744) 32
   `\j. mld_keypair_seedbuf 8 7 SEED (96 + j)` "s127" THEN
  ARM_STEPS_TAC KI87_EXEC (128--140) THEN
  KI87_BYTESN_TAC `sk:int64` 0 32 `mld_keypair_seedbuf 8 7 SEED` "s140" THEN
  KI87_BYTESN_TAC `sk:int64` 32 32
   `\j. mld_keypair_seedbuf 8 7 SEED (96 + j)` "s140" THEN
  KI87_BYTESN_TAC `sk:int64` 64 64 KI87_TR "s140" THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV
   (SPECL [`sk:int64`; `s140:armstate`; `2`; `8`; `7`; `mld_polyeta_pack_2`;
           `mld_polyeta_unpack_2`; `96`; `SEED:num`]
          MLD_KEYPAIR_SK_BYTES)) THEN
  REWRITE_TAC[GSYM mld_keypair_pk_87; GSYM mld_keypair_sk_87] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC; DISCH_TAC] THEN
  KI87_RUN_TAC KI87_EXEC "mldsa87_keypair_internal" "adrp3" KI87_ALLOWED 141 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[KI87_ZX_ZX] THEN
  REPEAT CONJ_TAC THEN PFS_EVENTS_TAC;;

let KI87_CASE_TAC b =
  KI87_PART1_TAC b THEN KI87_PART2_TAC b THEN KI87_PART3_TAC b THEN
  KI87_PART4_TAC THEN KI87_PART5_TAC b;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. The template of the events  *)
(* has one function for each case of the stack alignment, and rho and the    *)
(* declassified values are named rhov and D.                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_KEYPAIR_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN KI87_CALLEES_TAC THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(pk:int64) (sk:int64) (seed:int64) (rho:num) (D:num->bool list)
     (guard:int64) (mf:int64) (mc:int64) (pc:num) (stackpointer:int64)
     (returnaddress:int64).
     if aligned 32 stackpointer
     then f_ev_a pk sk seed rho D guard mf mc pc stackpointer returnaddress
     else f_ev_u pk sk seed rho D guard mf mc pc stackpointer returnaddress
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  ABBREV_TAC `rhov = mld_keypair_rho 8 7 SEED` THEN
  ABBREV_TAC `D = mld_keypair_declass_87 SEED` THEN
  KI87_SETUP_TAC THEN
  ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [REWRITE_TAC[ASSUME `aligned 32 (stackpointer:int64)`] THEN
    KI87_CASE_TAC 5344;
    REWRITE_TAC[ASSUME `~aligned 32 (stackpointer:int64)`] THEN
    KI87_CASE_TAC 5328]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_KEYPAIR_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_KEYPAIR_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_KEYPAIR_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_KEYPAIR_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL)
        th)));;
