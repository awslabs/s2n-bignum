(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/snappy/gcc12_O2/mem_copy64_spec.ml";;

(*** The bytes at src are split at the first call into the first 32 (the   ***)
(*** ghost y0 of the first memmove, its value at the call) and the rest,   ***)
(*** src + 32 .. src + size - 1 (x DIV 2^256), which the first memmove     ***)
(*** does not change: it is outside dst..dst+31 (MEM_COPY64_NONOVERLAP).    ***)
(*** The second memmove gets the 32 bytes at src + 32 at its call (the      ***)
(*** ghost y), of which the first size - 32 are x DIV 2^256.               ***)

let MEM_COPY64_NONOVERLAP = prove
 (`!(dst:int64) src k.
     32 <= k /\ nonoverlapping (dst,k) (src,k)
     ==> nonoverlapping (word_add src (word 32),k - 32) (dst,32)`,
  REWRITE_TAC[NONOVERLAPPING_MEMRANGE] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`src:int64`; `32`; `k - 32`; `k:num`]
    MEMRANGE_OFFSET_SUBSET) THEN
  MP_TAC(ISPECL [`dst:int64`; `32`; `k:num`] MEMRANGE_PREFIX_SUBSET) THEN
  ASM_SIMP_TAC[ARITH_RULE `32 <= k ==> 32 + k - 32 <= k`] THEN
  ASM SET_TAC[]);;

let MEM_COPY64_SPLIT = prove
 (`!(s:armstate) a k x.
     read (memory :> bytes(a,k)) s = x
     ==> read (memory :> bytes(a,MIN k 32)) s = x MOD 2 EXP 256 /\
         read (memory :> bytes(word_add a (word 32),k - 32)) s =
         x DIV 2 EXP 256`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[ARITH_RULE `256 = 8 * 32`; READ_BYTES_MOD; READ_BYTES_DIV]);;

let MEM_COPY64_PREFIX = prove
 (`!(s:armstate) a j y.
     j <= 32 /\ read (memory :> bytes(a,32)) s = y
     ==> read (memory :> bytes(a,j)) s = y MOD 2 EXP (8 * j)`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[READ_BYTES_MOD; ARITH_RULE `j <= 32 ==> MIN 32 j = j`]);;

let MEM_COPY64_JOIN = prove
 (`!(s:armstate) a j y0 y.
     read (memory :> bytes(a,32)) s = y0 /\
     read (memory :> bytes(word_add a (word 32),j)) s = y
     ==> read (memory :> bytes(a,32 + j)) s = y0 + 2 EXP 256 * y`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[READ_BYTES_COMBINE] THEN CONV_TAC NUM_REDUCE_CONV);;

let SNAPPY_MEM_COPY64_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (SNAPPY_MEM_COPY64_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  let exec = SNAPPY_MEM_COPY64_GCC12_O2_EXEC in
  let call y n =
    USE_THEN "H_MEMMOVE" (fun th ->
      ARM_BSTEP_PLT_STUB_TAC exec THEN
      ARM_BSTEP_CONTRACT_TAC exec th
       [`read events s`; `read X0 s`; `read X1 s`; `read X2 s`; y;
        `read X30 s`]
       ("s" ^ string_of_int n)) THEN
    MEMACCESS_INBOUNDS_TO_INSET_TAC in
  let ghost a k s y =
    X_CHOOSE_TAC y
     (prove(vsubst [a,`a:int64`; k,`k:num`; s,`s:armstate`]
              `?z. read (memory :> bytes(a,k)) s = z`,
            MESON_TAC[])) in
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; ALL] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (LABEL_TAC "H_MEMMOVE" o REWRITE_RULE[memmove_correct_safe_contract])
    STRIP_ASSUME_TAC) THEN
  CMP_HI_TAC `size:int64` `32` THEN
  ENSURES_INIT_TAC "s0" THEN
  ELF_RELOCATED_DATA_TAC ~defs:[snappy_libsnappy_gcc12_O2_relocated]
    ~select:(elf_slots_importing ["memmove"]) THEN
  ARM_BSTEP_TAC exec (1--9) THEN
  ghost `src:int64` `32` `s9:armstate` `y0:num` THEN
  ASM_CASES_TAC `32 < val(size:int64)` THENL
   [(* two memmoves *)
    SUBGOAL_THEN
     `x MOD 2 EXP 256 = y0 /\
      read (memory :> bytes(word_add src (word 32),val(size:int64) - 32)) s9 =
      x DIV 2 EXP 256`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(MATCH_MP MEM_COPY64_SPLIT
        (ASSUME `read (memory :> bytes(src,val(size:int64))) s9 = x`)) THEN
      ASM_SIMP_TAC[ARITH_RULE `32 < k ==> MIN k 32 = 32`] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `nonoverlapping (word_add src (word 32),val(size:int64) - 32)
                                 (dst:int64,32)` ASSUME_TAC THENL
     [MATCH_MP_TAC MEM_COPY64_NONOVERLAP THEN ASM_SIMP_TAC[LT_IMP_LE];
      ALL_TAC] THEN
    FIRST_ASSUM(ASSUME_TAC o ONCE_REWRITE_RULE[NONOVERLAPPING_MODULO_SYM] o
      check (fun th -> concl th = `nonoverlapping (word_add src (word 32),
               val(size:int64) - 32) (dst:int64,32)`)) THEN
    call `y0:num` 14 THEN
    ARM_BSTEP_TAC exec (15--23) THEN
    ghost `word_add src (word 32):int64` `32` `s23:armstate` `y:num` THEN
    SUBGOAL_THEN `y MOD 2 EXP (8 * (val(size:int64) - 32)) = x DIV 2 EXP 256`
    ASSUME_TAC THENL
     [MP_TAC(SPECL [`s23:armstate`; `word_add src (word 32):int64`;
                    `val(size:int64) - 32`; `y:num`] MEM_COPY64_PREFIX) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [(MP_TAC(ASSUME `val(size:int64) <= 64`) THEN ARITH_TAC); DISCH_THEN(ACCEPT_TAC o SYM)];
      ALL_TAC] THEN
    call `y:num` 28 THEN
    BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WORD_RULE `word_add (word_sub sp (word 48)) (word 48):int64 = sp`] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `val(size:int64) = 32 + (val size - 32)`
       (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THENL
       [(MP_TAC(ASSUME `32 < val(size:int64)`) THEN ARITH_TAC); ALL_TAC] THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `y0 + 2 EXP 256 * y MOD 2 EXP (8 * (val(size:int64) - 32))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MEM_COPY64_JOIN THEN CONJ_TAC THENL
         [ASM_REWRITE_TAC[];
          MATCH_MP_TAC MEM_COPY64_PREFIX THEN ASM_REWRITE_TAC[] THEN
          (MP_TAC(ASSUME `val(size:int64) <= 64`) THEN ARITH_TAC)];
        ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          concl th = `x MOD 2 EXP 256 = y0`)) THEN
        ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[DIVISION_SIMP]];
      MEMACCESS_INSET_TAC];
    (* one memmove *)
    SUBGOAL_THEN `y0 MOD 2 EXP (8 * val(size:int64)) = x` ASSUME_TAC THENL
     [MP_TAC(SPECL [`s9:armstate`; `src:int64`; `val(size:int64)`; `y0:num`]
        MEM_COPY64_PREFIX) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [(MP_TAC(ASSUME `~(32 < val(size:int64))`) THEN ARITH_TAC); DISCH_THEN(ACCEPT_TAC o SYM)];
      ALL_TAC] THEN
    call `y0:num` 14 THEN
    ARM_BSTEP_TAC exec (15--20) THEN
    BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WORD_RULE `word_add (word_sub sp (word 48)) (word 48):int64 = sp`] THEN
    CONJ_TAC THENL
     [MP_TAC(SPECL [`s20:armstate`; `dst:int64`; `val(size:int64)`; `y0:num`]
        MEM_COPY64_PREFIX) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [(MP_TAC(ASSUME `~(32 < val(size:int64))`) THEN ARITH_TAC); ASM_REWRITE_TAC[]]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
      MEMACCESS_INSET_TAC]]);;

let SNAPPY_MEM_COPY64_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (SNAPPY_MEM_COPY64_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  ENSURES_DROP_EVENTS_TAC SNAPPY_MEM_COPY64_GCC12_O2_IMAGE_SUBROUTINE_SAFE);;
