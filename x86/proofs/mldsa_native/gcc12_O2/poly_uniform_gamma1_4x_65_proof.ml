(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform sampling of the four polynomials of y for ML-DSA-65: the proof    *)
(* (see poly_uniform_gamma1_4x_65_spec.ml), a straight-line simulation with  *)
(* the FULL theorems of the callees. As for the x86 code of                  *)
(* mldsa_poly_uniform_4x, the frame is aligned to 32 bytes (see              *)
(* utils/mldsa_native_realign.ml); the code copies the seed with 128-bit SSE *)
(* loads and stores, the stores aligned (MOVAPS), and loads the nonces that  *)
(* the caller puts on the stack as 32-bit words.                             *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/poly_uniform_gamma1_4x_65_spec.ml";;
needs "x86/proofs/utils/mldsa_native_sampling.ml";;
needs "x86/proofs/utils/mldsa_native_realign.ml";;

let GAMMA1_4X_65_EXEC = MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_65_GCC12_O2_EXEC;;

let GAMMA1_4X_65_ALLOWED =
  [`pc:num`; `r0:int64`; `r1:int64`; `r2:int64`; `r3:int64`;
   `seed:int64`; `stackpointer:int64`; `returnaddress:int64`; `bot:int64`];;

let GAMMA1_4X_65_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc GAMMA1_4X_65_EXEC name
    (ilist @ [`pc:num`; `read RSP s`;
              `read (memory :> bytes64 (read RSP s)) s`])
    GAMMA1_4X_65_ALLOWED n;;

(* ------------------------------------------------------------------------- *)
(* The four seeds extended with the nonces: the inputs of SHAKE256, the      *)
(* absorbed states S0, ..., S3 and the streams as their bytes. The extended  *)
(* seeds are at 96-byte intervals in the aligned frame, below the state and  *)
(* the four buffers of 704 bytes for 5 blocks each.                          *)
(* ------------------------------------------------------------------------- *)

let GAMMA1_4X_65_NONCES =
  [`word_zx(n0:int64):int16`; `word_zx(n1:int64):int16`;
   `word_zx(n2:int64):int16`; `word_zx(n3:int64):int16`];;

let gamma1_4x_65_input h =
  vsubst [h,`h:int16`] `sd + 2 EXP 512 * val(h:int16)`;;

let gamma1_4x_65_stream h =
  mk_comb(`mld_shake256_stream 66`,gamma1_4x_65_input h);;

let GAMMA1_4X_65_SVS =
  [`S0:1600 word`; `S1:1600 word`; `S2:1600 word`; `S3:1600 word`];;

let GAMMA1_4X_65_EXT m =
  mk_comb(mk_comb(`word_add:int64->int64->int64`,`bot:int64`),
          mk_comb(`word:num->int64`,mk_small_numeral(488 + 96 * m)));;

(*** The seed at s0 as the four 128-bit words that the code loads, and the ***)
(*** nonces on the stack as the 32-bit words that it loads                  ***)

let GAMMA1_4X_65_SEED_TAC =
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

let GAMMA1_4X_65_STACKARGS_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (term_match []
             `read (memory :> bytes64 (word_add stackpointer (word k))) s =
              (n:int64)`) (concl th) &&
       is_var(rand(concl th)) &&
       mem (name_of(rand(concl th))) ["n1"; "n2"; "n3"]
    then ASSUME_TAC(MATCH_MP SAMPLING_READ_BYTES32_OF_64 th)
    else NO_TAC));;

(*** The 66 bytes of extended seed m at state s, from its 128-bit words ***)
(*** and the nonce h stored after them                                  ***)

let GAMMA1_4X_65_EXTSEED_TAC s m =
  let a = GAMMA1_4X_65_EXT m and h = el m GAMMA1_4X_65_NONCES in
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
      if can (term_match []
               `read (memory :> bytes(a,200)) s = val(x:1600 word)`)
             (concl th)
      then REWRITE_RULE abs th else th));;

(*** The blocks after squeezing, as bytes of the streams, those that ***)
(*** mldsa65_polyz_unpack reads, at addresses in the form of its     ***)
(*** precondition                                                     ***)

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
  SAMPLING_BYTES_NORMALIZE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The setup: the callee theorems, with the Keccak states as 200 bytes, the  *)
(* realigned stack frame (k = 4519, as 48 bytes are pushed before the AND,   *)
(* so that the aligned frame and the stacks of the callees are the region    *)
(* (bot,4488)), with RSP = bot + 424 aligned to 16 bytes after the frame is  *)
(* reserved, the saved registers and the absorbed states.                    *)
(* ------------------------------------------------------------------------- *)

let GAMMA1_4X_65_INTRO_TAC =
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
    MLDSA_NATIVE_POLYZ_UNPACK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_UNPACK" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst GAMMA1_4X_65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

let GAMMA1_4X_65_SETUP_TAC =
  REALIGN_TAC 4519 THEN REALIGN_ALIGNED_TAC [424] THEN
  REALIGN_FRAME_TAC 4567 4519 THEN
  REALIGN_NONOV_TAC 4488
   [`r0:int64,1024`; `r1:int64,1024`; `r2:int64,1024`; `r3:int64,1024`;
    `seed:int64,64`; `word pc:int64,51232`;
    `word_add stackpointer (word 4519):int64,48`;
    `word_add stackpointer (word 4567):int64,32`] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15` THEN
  GAMMA1_4X_65_STATES_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together. Each CALL is a     *)
(* step of its own, before the step of the callee, and RSP gets the value of *)
(* the AND after step 8; the YMM registers that the seed is loaded into are  *)
(* named at the start, so that the facts for their new low 128 bits are      *)
(* kept.                                                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  GAMMA1_4X_65_INTRO_TAC THEN GAMMA1_4X_65_SETUP_TAC THEN
  FULL_INIT_TAC THEN GAMMA1_4X_65_SEED_TAC THEN GAMMA1_4X_65_STACKARGS_TAC THEN
  SAMPLING_GHOST_REGS_TAC [`YMM0`; `YMM1`; `YMM2`; `YMM3`] "s0" THEN

  (*** The extended seeds and the absorbing ***)

  X86_STEPS_TAC GAMMA1_4X_65_EXEC (1--8) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC GAMMA1_4X_65_EXEC (9--46) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SAMPLING_SUBWORD_JOIN_128]) THEN
  SAMPLING_NONCE_BYTES_TAC THEN
  MAP_EVERY (GAMMA1_4X_65_EXTSEED_TAC `s46:x86state`) (0--3) THEN
  X86_STEPS_TAC GAMMA1_4X_65_EXEC (47--47) THEN
  GAMMA1_4X_65_CALL_TAC "H_INIT" [`read RDI s`] 48 THEN
  X86_STEPS_TAC GAMMA1_4X_65_EXEC (49--55) THEN
  GAMMA1_4X_65_CALL_TAC "H_ABSORB"
   ([`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `read R8 s`;
     `66`] @ map gamma1_4x_65_input GAMMA1_4X_65_NONCES) 56 THEN
  GAMMA1_4X_65_ABSORBED_TAC THEN

  (*** Squeezing five blocks of each ***)

  X86_STEPS_TAC GAMMA1_4X_65_EXEC (57--68) THEN
  GAMMA1_4X_65_CALL_TAC "H_SQUEEZE"
   ([`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `5`;
     `read R9 s`] @ GAMMA1_4X_65_SVS) 69 THEN
  GAMMA1_4X_65_BLOCKS_TAC THEN

  (*** Unpacking each polynomial from its blocks ***)

  MAP_EVERY (fun (m,(k,n)) ->
    X86_STEPS_TAC GAMMA1_4X_65_EXEC (k--n) THEN
    GAMMA1_4X_65_CALL_TAC "H_UNPACK"
     [`read RDI s`; `read RSI s`;
      gamma1_4x_65_stream (el m GAMMA1_4X_65_NONCES)] (n + 1))
   [0,(70,72); 1,(74,76); 2,(78,80); 3,(82,84)] THEN

  (*** Releasing the state, zeroing the buffers, the return ***)

  X86_STEPS_TAC GAMMA1_4X_65_EXEC (86--87) THEN
  GAMMA1_4X_65_CALL_TAC "H_RELEASE" [`read RDI s`] 88 THEN
  X86_STEPS_TAC GAMMA1_4X_65_EXEC (89--103) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[mld_poly_uniform_gamma1_19] THEN ASM_REWRITE_TAC[] THEN
  REALIGN_UNBOT_TAC THEN SAMPLING_PATH_DISCHARGE_SPINE_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
