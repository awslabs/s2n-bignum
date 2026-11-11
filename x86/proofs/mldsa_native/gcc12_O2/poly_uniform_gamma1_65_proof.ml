(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform sampling of one polynomial of y for ML-DSA-65: the proof (see     *)
(* poly_uniform_gamma1_65_spec.ml), a straight-line simulation with the FULL *)
(* theorems of the callees. As for the x86 code of mldsa_poly_uniform, the   *)
(* frame is aligned to 32 bytes (see utils/mldsa_native_realign.ml); the     *)
(* code copies the seed with 128-bit SSE loads and stores, the stores        *)
(* aligned (MOVAPS).                                                         *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/poly_uniform_gamma1_65_spec.ml";;
needs "x86/proofs/utils/mldsa_native_sampling.ml";;
needs "x86/proofs/utils/mldsa_native_realign.ml";;

let POLY_UNIFORM_GAMMA1_65_EXEC =
  MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_O2_EXEC;;

let POLY_UNIFORM_GAMMA1_65_ALLOWED =
  [`pc:num`; `a:int64`; `seed:int64`; `stackpointer:int64`;
   `returnaddress:int64`; `bot:int64`];;

let POLY_UNIFORM_GAMMA1_65_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc POLY_UNIFORM_GAMMA1_65_EXEC
    name (ilist @ [`pc:num`; `read RSP s`;
                   `read (memory :> bytes64 (read RSP s)) s`])
    POLY_UNIFORM_GAMMA1_65_ALLOWED n;;

(* ------------------------------------------------------------------------- *)
(* The seed extended with the nonce, the input M of SHAKE256, with the       *)
(* absorbed state S and the stream as its bytes. The extended seed is at the *)
(* bottom of the frame that the code reserves, below the context and the     *)
(* buffer of 680 bytes for 5 blocks.                                         *)
(* ------------------------------------------------------------------------- *)

let poly_uniform_gamma1_65_input =
  `sd + 2 EXP 512 * val(word_zx(nonce:int64):int16)`;;

let POLY_UNIFORM_GAMMA1_65_EXT = `word_add bot (word 328):int64`;;

(*** The seed at s0 as the four 128-bit words that the code loads ***)

let POLY_UNIFORM_GAMMA1_65_SEED_TAC =
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

(*** The 66 bytes of the extended seed at state s, from its 128-bit words ***)
(*** and the nonce stored after them, and the bound on them               ***)

let POLY_UNIFORM_GAMMA1_65_EXTSEED_TAC s =
  let a = POLY_UNIFORM_GAMMA1_65_EXT and h = `word_zx(nonce:int64):int16` in
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
(*** mldsa65_polyz_unpack reads, at addresses in the form of its    ***)
(*** precondition                                                    ***)

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
  SAMPLING_BYTES_NORMALIZE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The setup: the callee theorems, with the Keccak states as 200 bytes, the  *)
(* realigned stack frame (k = 1351, as 40 bytes are pushed before the AND,   *)
(* so that the aligned frame and the stacks of the callees are the region    *)
(* (bot,1320)), with RSP = bot + 328 aligned to 16 bytes after the frame is  *)
(* reserved, the saved registers and the absorbed state.                     *)
(* ------------------------------------------------------------------------- *)

let POLY_UNIFORM_GAMMA1_65_INTRO_TAC =
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
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst POLY_UNIFORM_GAMMA1_65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

let POLY_UNIFORM_GAMMA1_65_SETUP_TAC =
  REALIGN_TAC 1351 THEN REALIGN_ALIGNED_TAC [328] THEN
  REALIGN_FRAME_TAC 1391 1351 THEN
  REALIGN_NONOV_TAC 1320
   [`a:int64,1024`; `seed:int64,64`; `word pc:int64,51232`;
    `word_add stackpointer (word 1351):int64,40`;
    `word_add stackpointer (word 1391):int64,8`] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  POLY_UNIFORM_GAMMA1_65_STATE_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together. Each CALL is a     *)
(* step of its own, before the step of the callee, and RSP gets the value of *)
(* the AND after step 8; the YMM registers that the seed is loaded into are  *)
(* named at the start, so that the facts for their new low 128 bits are      *)
(* kept.                                                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  POLY_UNIFORM_GAMMA1_65_INTRO_TAC THEN POLY_UNIFORM_GAMMA1_65_SETUP_TAC THEN
  FULL_INIT_TAC THEN POLY_UNIFORM_GAMMA1_65_SEED_TAC THEN
  SAMPLING_GHOST_REGS_TAC [`YMM1`; `YMM2`; `YMM3`; `YMM4`] "s0" THEN

  (*** The extended seed, and the absorbing and finalizing ***)

  X86_STEPS_TAC POLY_UNIFORM_GAMMA1_65_EXEC (1--8) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC POLY_UNIFORM_GAMMA1_65_EXEC (9--22) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SAMPLING_SUBWORD_JOIN_128]) THEN
  SAMPLING_NONCE_BYTES_TAC THEN
  POLY_UNIFORM_GAMMA1_65_EXTSEED_TAC `s22:x86state` THEN
  X86_STEPS_TAC POLY_UNIFORM_GAMMA1_65_EXEC (23--23) THEN
  POLY_UNIFORM_GAMMA1_65_CALL_TAC "H_INIT" [`read RDI s`] 24 THEN
  X86_STEPS_TAC POLY_UNIFORM_GAMMA1_65_EXEC (25--28) THEN
  POLY_UNIFORM_GAMMA1_65_CALL_TAC "H_ABSORB"
   [`read RDI s`; `read RSI s`; `66`; `word 0:1600 word`; `0`;
    poly_uniform_gamma1_65_input] 29 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[POLY_UNIFORM_GAMMA1_65_ABSORB_POS;
                              ADD_CLAUSES]) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MOD_CONV)) THEN
  X86_STEPS_TAC POLY_UNIFORM_GAMMA1_65_EXEC (30--31) THEN
  POLY_UNIFORM_GAMMA1_65_CALL_TAC "H_FINALIZE"
   [`read RDI s`;
    mk_comb(`FST:1600 word#num->1600 word`,
            vsubst [poly_uniform_gamma1_65_input,`M:num`]
             `mld_keccak_absorb 136 (word 0) 0 66 M`);
    `66`] 32 THEN
  POLY_UNIFORM_GAMMA1_65_FINALIZED_TAC THEN

  (*** Squeezing five blocks and unpacking the polynomial ***)

  X86_STEPS_TAC POLY_UNIFORM_GAMMA1_65_EXEC (33--36) THEN
  POLY_UNIFORM_GAMMA1_65_CALL_TAC "H_SQUEEZE"
   [`read RDI s`; `680`; `read RDX s`; `S:1600 word`; `136`] 37 THEN
  POLY_UNIFORM_GAMMA1_65_BLOCKS_TAC THEN
  X86_STEPS_TAC POLY_UNIFORM_GAMMA1_65_EXEC (38--40) THEN
  POLY_UNIFORM_GAMMA1_65_CALL_TAC "H_UNPACK"
   [`read RDI s`; `read RSI s`;
    mk_comb(`mld_shake256_stream 66`,poly_uniform_gamma1_65_input)] 41 THEN

  (*** Releasing the state, zeroing the buffers, the return ***)

  X86_STEPS_TAC POLY_UNIFORM_GAMMA1_65_EXEC (42--43) THEN
  POLY_UNIFORM_GAMMA1_65_CALL_TAC "H_RELEASE" [`read RDI s`] 44 THEN
  X86_STEPS_TAC POLY_UNIFORM_GAMMA1_65_EXEC (45--62) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[mld_poly_uniform_gamma1_19] THEN ASM_REWRITE_TAC[] THEN
  REALIGN_UNBOT_TAC THEN SAMPLING_PATH_DISCHARGE_SPINE_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
