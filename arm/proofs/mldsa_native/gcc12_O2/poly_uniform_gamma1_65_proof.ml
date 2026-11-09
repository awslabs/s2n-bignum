(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform sampling of a polynomial of y for ML-DSA-65: the proof (see       *)
(* poly_uniform_gamma1_65_spec.ml), a straight-line simulation with the FULL *)
(* theorems of the callees. Absorbing the extended seed into the zero state  *)
(* and finalizing give the absorbed state of the 4-way functions             *)
(* (MLD_KECCAK_ABSORB_ONCE_SHORT), so that the bytes squeezed are those of   *)
(* mld_shake256_stream, as for mldsa65_poly_uniform_gamma1_4x.               *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/poly_uniform_gamma1_65_spec.ml";;
needs "arm/proofs/utils/mldsa_native_sampling.ml";;

let POLY_UNIFORM_GAMMA1_65_EXEC =
  MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_O2_EXEC;;

let POLY_UNIFORM_GAMMA1_65_ALLOWED =
  [`pc:num`; `a:int64`; `seed:int64`; `guard:int64`; `mf:int64`;
   `stackpointer:int64`; `returnaddress:int64`];;

let POLY_UNIFORM_GAMMA1_65_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc POLY_UNIFORM_GAMMA1_65_EXEC
    name ilist POLY_UNIFORM_GAMMA1_65_ALLOWED n;;

(* ------------------------------------------------------------------------- *)
(* The seed extended with the nonce, the input M of SHAKE256, with the       *)
(* absorbed state S and the stream as its bytes. The buffer of 680 bytes for *)
(* 5 blocks is aligned to 32 bytes within the stack frame, and the extended  *)
(* seed is 704 bytes after it.                                               *)
(* ------------------------------------------------------------------------- *)

let poly_uniform_gamma1_65_input =
  `sd + 2 EXP 512 * val(word_zx(nonce:int64):int16)`;;

let POLY_UNIFORM_GAMMA1_65_EXT =
  `word_add stackpointer
    (word((if aligned 32 stackpointer then 320 else 304) + 704)):int64`;;

let POLY_UNIFORM_GAMMA1_65_BUFFER_ADDRESS = SAMPLING_ALIGN32_RULE 335;;

let POLY_UNIFORM_GAMMA1_65_BUFFER_TAC =
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 335))
             (word 18446744073709551584):int64 =
    word_add stackpointer (word(if aligned 32 stackpointer then 320 else 304))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC POLY_UNIFORM_GAMMA1_65_BUFFER_ADDRESS THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

let POLY_UNIFORM_GAMMA1_65_NORMALIZE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th
    else th);;

(*** The GOT entries in the form in the preconditions of the callees ***)

let POLY_UNIFORM_GAMMA1_65_GOT_TAC =
  MAP_EVERY (fun n ->
    FIRST_ASSUM(fun th ->
      if can (term_match []
               (vsubst [n,`n:num`]
                 `read (memory :> bytes64
                         (word_add (word (pc:num)) (word n):int64)) s =
                  (g:int64)`)) (concl th)
      then ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD] th) else NO_TAC))
   [`got_stack_chk_guard:num`; `got_memset:num`];;

(*** The seed at s0 as the four 128-bit words that the code loads ***)

let POLY_UNIFORM_GAMMA1_65_SEED_TAC =
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

(*** The 66 bytes of the extended seed at state s, from its 128-bit words ***)
(*** and the nonce stored after them, and the bound on them               ***)

let POLY_UNIFORM_GAMMA1_65_EXTSEED_TAC s =
  let a = POLY_UNIFORM_GAMMA1_65_EXT and h = `word_zx(nonce:int64):int16` in
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
  MP_TAC(SPECL [a; `sd:num`; h; s] MLD_READ_BYTES66_NONCE16) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[SAMPLING_WORD_ZX_16];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [a; `66`; mk_comb(`read memory`,s)] READ_BYTES_BOUND) THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC;;

(*** The absorbed state as S, and the stream as its bytes ***)

let POLY_UNIFORM_GAMMA1_65_STATE_TAC =
  let t = vsubst [poly_uniform_gamma1_65_input,`M:num`]
           `mld_keccak_absorb_once 136 0x1F 66 M` in
  ABBREV_TAC(mk_eq(`S:1600 word`,t)) THEN
  ASSUME_TAC(SYM(REWRITE_RULE[ASSUME(mk_eq(t,`S:1600 word`))]
                  (SPECL [`66`; poly_uniform_gamma1_65_input]
                         mld_shake256_stream)));;

(*** The position after absorbing, and the state after finalizing ***)

let POLY_UNIFORM_GAMMA1_65_ABSORB_POS = prove
 (`!r (S:1600 word) pos inlen M.
        SND(mld_keccak_absorb r S pos inlen M) = (pos + inlen) MOD r`,
  REWRITE_TAC[mld_keccak_absorb] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[]);;

let POLY_UNIFORM_GAMMA1_65_FINALIZED_TAC =
  W(fun (asl,w) ->
    let bth = snd(find (fun (_,th) ->
                can (term_match [] (mk_comb(mk_comb(`(<):num->num->bool`,
                       poly_uniform_gamma1_65_input),`2 EXP (8 * 66)`)))
                    (concl th)) asl) in
    let lth = REWRITE_RULE[POLY_UNIFORM_GAMMA1_65_ABSORB_POS; ADD_CLAUSES]
               (MP (SPECL [`136`; `0x1F`; `66`; poly_uniform_gamma1_65_input]
                     MLD_KECCAK_ABSORB_ONCE_SHORT)
                   (CONJ (ARITH_RULE `66 + 2 <= 136`)
                     (CONJ (ARITH_RULE `0x1F < 128`) bth))) in
    let lth' = CONV_RULE(ONCE_DEPTH_CONV NUM_MOD_CONV) lth in
    RULE_ASSUM_TAC(REWRITE_RULE[lth'; ASSUME
      (mk_eq(vsubst [poly_uniform_gamma1_65_input,`M:num`]
               `mld_keccak_absorb_once 136 0x1F 66 M`,`S:1600 word`))]));;

(*** The blocks after squeezing, as bytes of the stream, those that ***)
(*** mldsa65_polyz_unpack reads                                    ***)

let POLY_UNIFORM_GAMMA1_65_BLOCKS_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes(a,n)) s =
                           num_of_bytelist(list_of_seq f n)`) (concl th)
    then ASSUME_TAC(MATCH_MP MLD_READ_BYTES_LIST_OF_SEQ th)
    else NO_TAC)) THEN
  W(fun (asl,w) ->
    let sts = filter (fun th -> can (term_match []
                `mld_keccak_squeeze_byte 136 S 136 = mld_shake256_stream n m`)
                (concl th)) (map snd asl) in
    RULE_ASSUM_TAC(fun th ->
      if can (term_match [] `!j. j < 680 ==> P j`) (concl th)
      then SAMPLING_BOUND_RULE 640 (REWRITE_RULE sts th)
      else th)) THEN
  POLY_UNIFORM_GAMMA1_65_NORMALIZE_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together.                    *)
(* ------------------------------------------------------------------------- *)

let POLY_UNIFORM_GAMMA1_65_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] th)
     "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE256_INIT_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_INIT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE256_ABSORB_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_ABSORB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE256_FINALIZE_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_FINALIZE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_SQUEEZE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE256_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_RELEASE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYZ_UNPACK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_UNPACK" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst POLY_UNIFORM_GAMMA1_65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

let POLY_UNIFORM_GAMMA1_65_SETUP_TAC =
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 1328):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `304 <= (if aligned 32 (stackpointer:int64) then 320 else 304) /\
    (if aligned 32 (stackpointer:int64) then 320 else 304) <= 320`
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
     (mk_const(r,[]))) (19--22) THEN
  POLY_UNIFORM_GAMMA1_65_STATE_TAC;;

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  POLY_UNIFORM_GAMMA1_65_INTRO_TAC THEN POLY_UNIFORM_GAMMA1_65_SETUP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN POLY_UNIFORM_GAMMA1_65_SEED_TAC THEN

  (*** The extended seed, and the absorbing and finalizing ***)

  ARM_STEPS_TAC POLY_UNIFORM_GAMMA1_65_EXEC (1--2) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC POLY_UNIFORM_GAMMA1_65_EXEC (3--6) THEN
  POLY_UNIFORM_GAMMA1_65_BUFFER_TAC THEN
  ARM_STEPS_TAC POLY_UNIFORM_GAMMA1_65_EXEC (7--21) THEN
  POLY_UNIFORM_GAMMA1_65_NORMALIZE_TAC THEN
  POLY_UNIFORM_GAMMA1_65_EXTSEED_TAC `s21:armstate` THEN
  POLY_UNIFORM_GAMMA1_65_CALL_TAC "H_INIT"
   [`read X0 s`; `pc:num`; `read X30 s`] 22 THEN
  ARM_STEPS_TAC POLY_UNIFORM_GAMMA1_65_EXEC (23--26) THEN
  POLY_UNIFORM_GAMMA1_65_CALL_TAC "H_ABSORB"
   [`read X0 s`; `read X1 s`; `66`; `word 0:1600 word`; `0`;
    poly_uniform_gamma1_65_input; `pc:num`; `read SP s`; `read X30 s`] 27
  THEN
  RULE_ASSUM_TAC(REWRITE_RULE[POLY_UNIFORM_GAMMA1_65_ABSORB_POS;
                              ADD_CLAUSES]) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MOD_CONV)) THEN
  ARM_STEPS_TAC POLY_UNIFORM_GAMMA1_65_EXEC (28--29) THEN
  POLY_UNIFORM_GAMMA1_65_GOT_TAC THEN
  POLY_UNIFORM_GAMMA1_65_CALL_TAC "H_FINALIZE"
   [`read X0 s`;
    mk_comb(`FST:1600 word#num->1600 word`,
            vsubst [poly_uniform_gamma1_65_input,`M:num`]
             `mld_keccak_absorb 136 (word 0) 0 66 M`);
    `66`; `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 30 THEN
  POLY_UNIFORM_GAMMA1_65_FINALIZED_TAC THEN

  (*** Squeezing five blocks and unpacking the polynomial ***)

  ARM_STEPS_TAC POLY_UNIFORM_GAMMA1_65_EXEC (31--34) THEN
  POLY_UNIFORM_GAMMA1_65_CALL_TAC "H_SQUEEZE"
   [`read X0 s`; `680`; `read X2 s`; `S:1600 word`; `136`; `pc:num`;
    `read SP s`; `read X30 s`] 35 THEN
  POLY_UNIFORM_GAMMA1_65_BLOCKS_TAC THEN
  ARM_STEPS_TAC POLY_UNIFORM_GAMMA1_65_EXEC (36--38) THEN
  POLY_UNIFORM_GAMMA1_65_CALL_TAC "H_UNPACK"
   [`read X0 s`; `read X1 s`;
    mk_comb(`mld_shake256_stream 66`,poly_uniform_gamma1_65_input);
    `pc:num`; `read X30 s`] 39 THEN

  (*** Releasing the state, zeroing the buffers, the return ***)

  ARM_STEPS_TAC POLY_UNIFORM_GAMMA1_65_EXEC (40--41) THEN
  POLY_UNIFORM_GAMMA1_65_CALL_TAC "H_RELEASE"
   [`read X0 s`; `pc:num`; `read X30 s`] 42 THEN
  ARM_STEPS_TAC POLY_UNIFORM_GAMMA1_65_EXEC (43--46) THEN
  LIBC_PLT_TAC POLY_UNIFORM_GAMMA1_65_EXEC 46 THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" POLY_UNIFORM_GAMMA1_65_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref POLY_UNIFORM_GAMMA1_65_ALLOWED) 51 THEN
  ARM_STEPS_TAC POLY_UNIFORM_GAMMA1_65_EXEC (52--56) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC POLY_UNIFORM_GAMMA1_65_EXEC (57--67) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[mld_poly_uniform_gamma1_19] THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;
