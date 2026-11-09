(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform sampling of the four polynomials of y for ML-DSA-65: the proof    *)
(* (see poly_uniform_gamma1_4x_65_spec.ml), a straight-line simulation with  *)
(* the FULL theorems of the callees.                                         *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/poly_uniform_gamma1_4x_65_spec.ml";;
needs "arm/proofs/utils/mldsa_native_sampling.ml";;

let GAMMA1_4X_65_EXEC = MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_65_GCC12_O2_EXEC;;

let GAMMA1_4X_65_ALLOWED =
  [`pc:num`; `r0:int64`; `r1:int64`; `r2:int64`; `r3:int64`;
   `seed:int64`; `guard:int64`; `mf:int64`; `stackpointer:int64`;
   `returnaddress:int64`];;

let GAMMA1_4X_65_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc GAMMA1_4X_65_EXEC name
    ilist GAMMA1_4X_65_ALLOWED n;;

(* ------------------------------------------------------------------------- *)
(* The four seeds extended with the nonces: the inputs of SHAKE256, the      *)
(* absorbed states S0, ..., S3 and the streams as their bytes. The extended  *)
(* seeds are at 96-byte intervals after the four buffers of 704 bytes for 5  *)
(* blocks each, which are aligned to 32 bytes within the stack frame.        *)
(* ------------------------------------------------------------------------- *)

let GAMMA1_4X_65_NONCES =
  [`word_zx(n0:int64):int16`; `word_zx(n1:int64):int16`;
   `word_zx(n2:int64):int16`; `n3:int16`];;

let gamma1_4x_65_input h =
  vsubst [h,`h:int16`] `sd + 2 EXP 512 * val(h:int16)`;;

let gamma1_4x_65_stream h =
  mk_comb(`mld_shake256_stream 66`,gamma1_4x_65_input h);;

let GAMMA1_4X_65_SVS =
  [`S0:1600 word`; `S1:1600 word`; `S2:1600 word`; `S3:1600 word`];;

let GAMMA1_4X_65_EXT m =
  let off = mk_binop `(+):num->num->num`
              `if aligned 32 (stackpointer:int64) then 448 else 432`
              (mk_small_numeral(2816 + 96 * m)) in
  mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
          mk_comb(`word:num->int64`,off));;

let GAMMA1_4X_65_BUFFER_ADDRESS = SAMPLING_ALIGN32_RULE 463;;

let GAMMA1_4X_65_BUFFER_TAC =
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 463))
             (word 18446744073709551584):int64 =
    word_add stackpointer (word(if aligned 32 stackpointer then 448 else 432))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC GAMMA1_4X_65_BUFFER_ADDRESS THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

let GAMMA1_4X_65_NORMALIZE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th
    else th);;

(*** The GOT entries in the form in the preconditions of the callees ***)

let GAMMA1_4X_65_GOT_TAC =
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

let GAMMA1_4X_65_SEED_TAC =
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

(*** The 66 bytes of extended seed m at state s, from its 128-bit words ***)
(*** and the nonce h stored after them                                  ***)

let GAMMA1_4X_65_EXTSEED_TAC s m =
  let a = GAMMA1_4X_65_EXT m and h = el m GAMMA1_4X_65_NONCES in
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
    DISCH_TAC];;

(*** The absorbed states as S0, ..., S3, and the streams as their bytes ***)

let GAMMA1_4X_65_STATES_TAC =
  MAP_EVERY (fun (h,sv) ->
    let t = vsubst [gamma1_4x_65_input h,`M:num`]
             `mld_keccak_absorb_once 136 0x1F 66 M` in
    ABBREV_TAC(mk_eq(sv,t)) THEN
    ASSUME_TAC(SYM(REWRITE_RULE[ASSUME(mk_eq(t,sv))]
                    (SPECL [`66`; gamma1_4x_65_input h] mld_shake256_stream))))
   (zip GAMMA1_4X_65_NONCES GAMMA1_4X_65_SVS);;

let GAMMA1_4X_65_ABSORBED_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM MLD_KECCAK_ABSORB_ONCE]) THEN
  W(fun (asl,w) ->
    let abs = filter (fun th -> can (term_match []
                `mld_keccak_absorb_once r p n m = (S:1600 word)`) (concl th))
               (map snd asl) in
    RULE_ASSUM_TAC(fun th ->
      if can (term_match [] `read (memory :> wbytes a) s = (x:1600 word)`)
             (concl th)
      then REWRITE_RULE abs th else th));;

(*** The blocks after squeezing, as bytes of the streams, those that ***)
(*** mldsa65_polyz_unpack reads                                       ***)

let GAMMA1_4X_65_BLOCKS_TAC =
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
      then SAMPLING_BOUND_RULE 640
            (CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) (REWRITE_RULE sts th))
      else th)) THEN
  GAMMA1_4X_65_NORMALIZE_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together.                    *)
(* ------------------------------------------------------------------------- *)

let GAMMA1_4X_65_INTRO_TAC =
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
    MLDSA_NATIVE_POLYZ_UNPACK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_UNPACK" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst GAMMA1_4X_65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

let GAMMA1_4X_65_SETUP_TAC =
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 4464):int64)` THEN
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
     (mk_const(r,[]))) (19--28) THEN
  GAMMA1_4X_65_STATES_TAC;;

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  GAMMA1_4X_65_INTRO_TAC THEN GAMMA1_4X_65_SETUP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN GAMMA1_4X_65_SEED_TAC THEN

  (*** The extended seeds and the absorbing ***)

  ARM_STEPS_TAC GAMMA1_4X_65_EXEC (1--4) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC GAMMA1_4X_65_EXEC (5--9) THEN GAMMA1_4X_65_BUFFER_TAC THEN
  ARM_STEPS_TAC GAMMA1_4X_65_EXEC (10--46) THEN GAMMA1_4X_65_NORMALIZE_TAC THEN
  MAP_EVERY (GAMMA1_4X_65_EXTSEED_TAC `s46:armstate`) (0--3) THEN
  GAMMA1_4X_65_CALL_TAC "H_INIT" [`read X0 s`; `pc:num`; `read X30 s`] 47
  THEN
  ARM_STEPS_TAC GAMMA1_4X_65_EXEC (48--54) THEN GAMMA1_4X_65_GOT_TAC THEN
  GAMMA1_4X_65_CALL_TAC "H_ABSORB"
   ([`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
     `66`] @ map gamma1_4x_65_input GAMMA1_4X_65_NONCES @
    [`guard:int64`; `pc:num`; `read SP s`; `read X30 s`]) 55 THEN
  GAMMA1_4X_65_ABSORBED_TAC THEN

  (*** Squeezing five blocks of each ***)

  ARM_STEPS_TAC GAMMA1_4X_65_EXEC (56--62) THEN
  GAMMA1_4X_65_CALL_TAC "H_SQUEEZE"
   ([`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `5`;
     `read X5 s`] @ GAMMA1_4X_65_SVS @
    [`pc:num`; `read SP s`; `read X30 s`]) 63 THEN
  GAMMA1_4X_65_BLOCKS_TAC THEN

  (*** Unpacking each polynomial from its blocks ***)

  MAP_EVERY (fun (m,(k,n)) ->
    ARM_STEPS_TAC GAMMA1_4X_65_EXEC (k--n) THEN
    GAMMA1_4X_65_CALL_TAC "H_UNPACK"
     [`read X0 s`; `read X1 s`;
      gamma1_4x_65_stream (el m GAMMA1_4X_65_NONCES); `pc:num`;
      `read X30 s`] (n + 1))
   [0,(64,66); 1,(68,70); 2,(72,74); 3,(76,78)] THEN

  (*** Releasing the state, zeroing the buffers, the return ***)

  ARM_STEPS_TAC GAMMA1_4X_65_EXEC (80--81) THEN
  GAMMA1_4X_65_CALL_TAC "H_RELEASE"
   [`read X0 s`; `pc:num`; `read SP s`; `read X30 s`] 82 THEN
  ARM_STEPS_TAC GAMMA1_4X_65_EXEC (83--86) THEN
  LIBC_PLT_TAC GAMMA1_4X_65_EXEC 86 THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" GAMMA1_4X_65_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref GAMMA1_4X_65_ALLOWED) 91 THEN
  ARM_STEPS_TAC GAMMA1_4X_65_EXEC (92--95) THEN
  LIBC_PLT_TAC GAMMA1_4X_65_EXEC 95 THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" GAMMA1_4X_65_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref GAMMA1_4X_65_ALLOWED) 100 THEN
  ARM_STEPS_TAC GAMMA1_4X_65_EXEC (101--101) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC GAMMA1_4X_65_EXEC (102--116) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[mld_poly_uniform_gamma1_19] THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_65_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_65_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;
