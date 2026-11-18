(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/gcc12_Os/check_pk_k2_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/polyvec_frombytes_k2_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/polyvec_reduce_k2_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/polyvec_tobytes_k2_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/ct_memcmp_2_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/zeroize_5_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The reduced vector, as a list of 16-bit coefficients for the encoding,    *)
(* and the equivalence of its encoding with the key with the 12-bit fields   *)
(* of the key being below 3329.                                              *)
(* ------------------------------------------------------------------------- *)

let CHECKPK_BYTES16_LIST = prove
 (`!a n (f:num->int16) s:armstate.
        (!i. i < n
             ==> read (memory :> bytes16(word_add a (word(2 * i)))) s = f i)
        ==> read (memory :> bytes(a,2 * n)) s =
            num_of_wordlist(list_of_seq f n)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL;
                list_of_seq; num_of_wordlist];
    REPEAT STRIP_TAC] THEN
  REWRITE_TAC[ARITH_RULE `2 * SUC n = 2 * n + 2`; READ_COMPONENT_COMPOSE;
              READ_BYTES_COMBINE; list_of_seq] THEN
  REWRITE_TAC[NUM_OF_WORDLIST_APPEND; LENGTH_LIST_OF_SEQ;
              NUM_OF_WORDLIST_SING; DIMINDEX_16] THEN
  BINOP_TAC THENL
   [REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[ARITH_RULE `8 * 2 * n = 16 * n`] THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    REWRITE_TAC[ARITH_RULE `n < SUC n`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[BYTES16_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
                DIMINDEX_16] THEN
    CONV_TAC NUM_REDUCE_CONV]);;

let CHECKPK_IVAL_WORD = prove
 (`!f. f < 32768 ==> ival(word f:int16) = &f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ival; VAL_WORD; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `f < 32768 ==> f < 65536`]);;

let CHECKPK_REDUCED = prove
 (`!(x:int16) f.
        f < 2 EXP 12 /\ ival x = ival(word f:int16) rem &3329
        ==> x = word(f MOD 3329)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ival(word f:int16) = &f` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC CHECKPK_IVAL_WORD THEN UNDISCH_TAC `f < 2 EXP 12` THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_OF_NUM_REM]) THEN
  ONCE_REWRITE_TAC[GSYM IVAL_EQ] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CHECKPK_IVAL_WORD THEN
  MP_TAC(SPECL [`f:num`; `3329`] MOD_LT_EQ) THEN ARITH_TAC);;

let CHECKPK_LIST_PROPS = prove
 (`!(g:num->num) l.
        LENGTH(list_of_seq (\i. word(g i MOD 3329):int16) l) = l /\
        ALL (\x. val x < 4096) (list_of_seq (\i. word(g i MOD 3329):int16) l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH_LIST_OF_SEQ; GSYM ALL_EL] THEN
  SIMP_TAC[LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ; VAL_WORD; DIMINDEX_16] THEN
  REPEAT STRIP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(SPECL [`(g:num->num) i`; `3329`] MOD_LT_EQ) THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `x < 3329 ==> x < 65536`] THEN ARITH_TAC);;

let CHECKPK_REENCODE = prove
 (`!l n. n < 2 EXP (12 * l)
         ==> (n = num_of_wordlist(MAP (word_zx:int16->12 word)
                    (list_of_seq (\i. word(((n DIV 2 EXP (12 * i)) MOD
                                            2 EXP 12) MOD 3329):int16) l)) <=>
              !i. i < l ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MAP_LIST_OF_SEQ; o_DEF] THEN
  SUBGOAL_THEN
   `!x. word_zx(word(x MOD 3329):int16):12 word = word(x MOD 3329)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(ARITH_RULE `x MOD 3329 < 3329`) THEN
    SIMP_TAC[MOD_LT; ARITH_RULE `y < 3329 ==> y < 65536`];
    ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(REWRITE_RULE[DIMINDEX_CONV `dimindex(:12)`; LENGTH_LIST_OF_SEQ]
     (ISPECL [`list_of_seq (\x. word((n DIV 2 EXP (12 * x)) MOD 2 EXP 12 MOD
                                     3329):12 word) l`; `i:num`]
             NUM_OF_WORDLIST_EL)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check
     (fun th -> is_eq(concl th) && lhs(concl th) = `n:num`)) THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ; VAL_WORD] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    SPEC_TAC(`(n DIV 2 EXP (12 * i)) MOD 4096`,`d:num`) THEN GEN_TAC THEN
    MP_TAC(ARITH_RULE `d MOD 3329 < 3329`) THEN
    SIMP_TAC[MOD_LT; ARITH_RULE `y < 3329 ==> y < 4096`] THEN MESON_TAC[];
    DISCH_TAC] THEN
  MP_TAC(REWRITE_RULE[DIMINDEX_CONV `dimindex(:12)`]
    (ISPECL [`l:num`; `n:num`]
      (INST_TYPE [`:12`,`:N`] NUM_OF_WORDLIST_OF_NUM_EQ_SELF))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th] THEN
                       ASSUME_TAC th) THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_WORDLIST_OF_NUM; LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  MP_TAC(ISPECL [`wordlist_of_num l n:(12 word)list`; `i:num`]
                EL_NUM_OF_WORDLIST) THEN
  ASM_REWRITE_TAC[LENGTH_WORDLIST_OF_NUM; DIMINDEX_CONV `dimindex(:12)`] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[MOD_LT; MOD_MOD_REFL]);;

let CHECKPK_ALIGNED_16_32 = prove
 (`(!x:int64. aligned 16 x <=> word_and x (word 15) = word 0) /\
   (!x:int64. aligned 32 x <=> word_and x (word 31) = word 0)`,
  CONJ_TAC THEN GEN_TAC THEN REWRITE_TAC[aligned; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`x:int64`; `4`] (CONJUNCT1 WORD_AND_MASK_WORD));
    MP_TAC(ISPECL [`x:int64`; `5`] (CONJUNCT1 WORD_AND_MASK_WORD))] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIVIDES_MOD; GSYM VAL_EQ_0; VAL_WORD; DIMINDEX_64] THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `x MOD 16 < 16`; ARITH_RULE `x MOD 32 < 32`;
           ARITH_RULE `x < 16 ==> x < 2 EXP 64`;
           ARITH_RULE `x < 32 ==> x < 2 EXP 64`]);;

let CHECKPK_BUFFER_ADDRESS = prove
 (`!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 95)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 64 else 80))`,
  REWRITE_TAC[CHECKPK_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;


(* ------------------------------------------------------------------------- *)
(* The buffers are aligned to 32 bytes within the stack frame, so their      *)
(* address depends on whether the stack pointer is a multiple of 32 or just  *)
(* of 16. The proof uses a variable boff for the offset of the first one.    *)
(* ------------------------------------------------------------------------- *)

let CHECKPK_BUFFER_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) &&
       can (term_match [] `word_and (word_add stackpointer (word n))
                                    (word m):int64`) (lhs(concl th))
    then SUBST_ALL_TAC th else NO_TAC);;

let CHECKPK_NORMALIZE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th
    else th);;

(* ------------------------------------------------------------------------- *)
(* The callees.                                                              *)
(* ------------------------------------------------------------------------- *)

let LOCAL_FROMBYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_REDUCE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_POLYVEC_REDUCE_K2_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_TOBYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_POLYVEC_TOBYTES_K2_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_MEMCMP_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_CT_MEMCMP_2_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_ZEROIZE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_ZEROIZE_5_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* The setup, with the offset of the buffers as boff.                        *)
(* ------------------------------------------------------------------------- *)

let CHECKPK_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`pk:int64`; `n:num`; `guard:int64`; `mf:int64`; `ea:int64`; `el:num`;
    `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 1888 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> ASSUME_TAC th THEN
              LABEL_TAC "H_MEMSET" (REWRITE_RULE[memset_contract] th))
   (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 1888):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP CHECKPK_BUFFER_ADDRESS
          (ASSUME `aligned 16 (stackpointer:int64)`)) THEN
  SUBGOAL_THEN
   `64 <= (if aligned 32 (stackpointer:int64) then 64 else 80) /\
    (if aligned 32 (stackpointer:int64) then 64 else 80) <= 80`
  MP_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`if aligned 32 (stackpointer:int64) then 64 else 80`,
           `boff:num`) THEN
  GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memset:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21`;;

(*** The reduced vector as a list, and as the number of its encoding ***)

let CHECKPK_L =
 `list_of_seq (\i. word(((n DIV 2 EXP (12 * i)) MOD 2 EXP 12) MOD 3329):int16)
              512`;;

let CHECKPK_M =
 `num_of_wordlist(MAP (word_zx:int16->12 word)
   (list_of_seq (\i. word(((n DIV 2 EXP (12 * i)) MOD 2 EXP 12) MOD 3329))
                512))`;;

let CHECKPK_LIST_TAC s =
  SUBGOAL_THEN (vsubst [s,`s:armstate`]
   `read (memory :> bytes(word_add stackpointer (word boff),1024)) s =
    num_of_wordlist(list_of_seq (\i. word(((n DIV 2 EXP (12 * i)) MOD
                                           2 EXP 12) MOD 3329):int16) 512)`)
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1024 = 2 * 512`] THEN
    MATCH_MP_TAC CHECKPK_BYTES16_LIST THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC CHECKPK_REDUCED THEN
    REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    FIRST_ASSUM(fun th -> MATCH_MP_TAC th) THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

let CHECKPK_BOUND a s =
  REWRITE_RULE[GSYM READ_COMPONENT_COMPOSE]
   (ISPECL [a; `768`; mk_comb(`read memory:armstate->int64->byte`,s)]
           READ_BYTES_BOUND);;

(*** The GOT entry of memset in the form in the precondition of mlk_zeroize ***)

let CHECKPK_GOT_TAC =
  W(fun (asl,_) ->
    MAP_EVERY (fun (_,th) ->
      if can (term_match []
           `read (memory :> bytes64 (word_add (word pc) (word n))) s = g`)
           (concl th)
      then ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD] th) else ALL_TAC) asl);;

(*** The result: the number n of the key equals the number of the encoding of
     its reduction if and only if all its 12-bit fields are below 3329 ***)

let CHECKPK_RESULT_TAC s =
  SUBGOAL_THEN `n < 2 EXP (12 * 512)` ASSUME_TAC THENL
   [MP_TAC(CHECKPK_BOUND `pk:int64` s) THEN
    ASM_REWRITE_TAC[ARITH_RULE `12 * 512 = 8 * 768`];
    ALL_TAC] THEN
  MP_TAC(SPECL [`512`; `n:num`] CHECKPK_REENCODE) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  W(fun (_,w) -> SPEC_TAC(find_term is_forall w,`c:bool`)) THEN
  GEN_TAC THEN BOOL_CASES_TAC `c:bool` THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
  REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV;;

(* ------------------------------------------------------------------------- *)
(* The correctness proof.                                                    *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  CHECKPK_INTRO_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_EXEC (1--5) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_EXEC (6--8) THEN
  CHECKPK_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_EXEC (9--14) THEN

  (*** Decoding, reducing and encoding the vector ***)

  LOCAL_FROMBYTES_TAC [`read X0 s`; `read X1 s`; `n:num`; `pc:num`;
                       `read SP s`; `read X30 s`] 15 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_EXEC (16--18) THEN
  LOCAL_REDUCE_TAC [`read X0 s`;
    `\i. word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12):int16`;
    `pc:num`; `read SP s`; `read X30 s`] 19 THEN
  CHECKPK_LIST_TAC `s19:armstate` THEN CHECKPK_NORMALIZE_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_EXEC (20--22) THEN
  LOCAL_TOBYTES_TAC [`read X0 s`; `read X1 s`; CHECKPK_L; `pc:num`;
                     `read SP s`; `read X30 s`] 23 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CHECKPK_LIST_PROPS]) THEN

  (*** The comparison with the key and the zeroing of the buffers ***)

  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_EXEC (24--27) THEN
  CHECKPK_NORMALIZE_TAC THEN
  LOCAL_MEMCMP_TAC [`read X0 s`; `read X1 s`; `768`; `n:num`; CHECKPK_M;
                    `pc:num`; `read X30 s`] 28 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_EXEC (29--34) THEN
  CHECKPK_NORMALIZE_TAC THEN CHECKPK_GOT_TAC THEN
  LOCAL_ZEROIZE_TAC [`read X0 s`; `768`; `mf:int64`; `ea:int64`; `el:num`;
                     `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 35 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_EXEC (36--38) THEN
  CHECKPK_NORMALIZE_TAC THEN CHECKPK_GOT_TAC THEN
  LOCAL_ZEROIZE_TAC [`read X0 s`; `1024`; `mf:int64`; `ea:int64`; `el:num`;
                     `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 39 THEN

  (*** The stack guard and the return ***)

  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_EXEC (40--40) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_EXEC (41--51) THEN
  CHECKPK_NORMALIZE_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CHECKPK_RESULT_TAC `s51:armstate`);;

(* ------------------------------------------------------------------------- *)
(* The combined correctness, constant-time and memory safety proof, from the *)
(* combined theorems of the callees, except for mlk_zeroize_5, whose result *)
(* is not needed. The offset boff of the buffers is an abbreviation of the   *)
(* conditional, which is restored before the events are matched, so that     *)
(* they are a function of the stack pointer.                                 *)
(* ------------------------------------------------------------------------- *)

let CHECKPK_ALLOWED =
  [`pc:num`; `pk:int64`; `guard:int64`; `mf:int64`;
   `stackpointer:int64`; `returnaddress:int64`; `boff:num`];;

let CHECKPK_UNABBREV_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
   (fun th -> is_eq(concl th) && rhs(concl th) = `boff:num`));;

let CHECKPK_CALL_TAC name ilist n =
  CHECKPK_NORMALIZE_TAC THEN CHECKPK_GOT_TAC THEN
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_Os_mc,
       MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_Os_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref CHECKPK_ALLOWED); LABEL_TAC name safety_th]);;

let CHECKPK_FULL_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLKEM_NATIVE_ZEROIZE_5_GCC12_OS_IMAGE_SUBROUTINE_SAFE th)
     "H_ZEROIZE") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_GCC12_OS_IMAGE_SUBROUTINE_FULL
    "H_FROMBYTES" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_REDUCE_K2_GCC12_OS_IMAGE_SUBROUTINE_FULL
    "H_REDUCE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_TOBYTES_K2_GCC12_OS_IMAGE_SUBROUTINE_FULL
    "H_TOBYTES" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_CT_MEMCMP_2_GCC12_OS_IMAGE_SUBROUTINE_FULL
    "H_MEMCMP" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 1888):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ASSUME_TAC(MATCH_MP CHECKPK_BUFFER_ADDRESS
              (ASSUME `aligned 16 (stackpointer:int64)`)) THEN
  SUBGOAL_THEN
   `64 <= (if aligned 32 (stackpointer:int64) then 64 else 80) /\
    (if aligned 32 (stackpointer:int64) then 64 else 80) <= 80`
  STRIP_ASSUME_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `boff = if aligned 32 (stackpointer:int64) then 64 else 80` THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memset:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21`;;

let MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_IMAGE_SUBROUTINE_FULL = prove
 (MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  CHECKPK_FULL_INTRO_TAC THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_EXEC (1--5) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_EXEC (6--8) THEN
  CHECKPK_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_EXEC (9--14) THEN

  (*** Decoding, reducing and encoding the vector ***)

  CHECKPK_CALL_TAC "H_FROMBYTES"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `n:num`; `pc:num`;
    `read SP s`; `read X30 s`] 15 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_EXEC (16--18) THEN
  CHECKPK_CALL_TAC "H_REDUCE"
   [`e:(uarch_event)list`; `read X0 s`;
    `\i. word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12):int16`;
    `pc:num`; `read SP s`; `read X30 s`] 19 THEN
  CHECKPK_LIST_TAC `s19:armstate` THEN CHECKPK_NORMALIZE_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_EXEC (20--22) THEN
  CHECKPK_CALL_TAC "H_TOBYTES"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; CHECKPK_L; `pc:num`;
    `read SP s`; `read X30 s`] 23 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CHECKPK_LIST_PROPS]) THEN

  (*** The comparison with the key and the zeroing of the buffers ***)

  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_EXEC (24--27) THEN
  CHECKPK_CALL_TAC "H_MEMCMP"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `768`; `n:num`;
    CHECKPK_M; `pc:num`; `read X30 s`] 28 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_EXEC (29--34) THEN
  CHECKPK_CALL_TAC "H_ZEROIZE"
   [`e:(uarch_event)list`; `read X0 s`; `768`; `pc:num`; `read SP s`;
    `read X30 s`] 35 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_EXEC (36--38) THEN
  CHECKPK_CALL_TAC "H_ZEROIZE"
   [`e:(uarch_event)list`; `read X0 s`; `1024`; `pc:num`; `read SP s`;
    `read X30 s`] 39 THEN

  (*** The stack guard and the return ***)

  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_EXEC (40--40) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_EXEC (41--51) THEN
  CHECKPK_NORMALIZE_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [CHECKPK_RESULT_TAC `s51:armstate`;
    CHECKPK_UNABBREV_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The constant-time and memory safety theorem is the combined one without   *)
(* the result.                                                               *)
(* ------------------------------------------------------------------------- *)

let ENSURES_PREPOST_WEAKEN = MESON[ENSURES_PREPOSTCONDITION_THM]
 `ensures step P Q C
  ==> (!x. P' x ==> P x) /\ (!x. Q x ==> Q' x)
      ==> ensures step P' Q' C`;;

let MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_IMAGE_SUBROUTINE_SAFE = prove
 (MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP
   MLKEM_NATIVE_CHECK_PK_K2_GCC12_OS_IMAGE_SUBROUTINE_FULL) THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GHOST_INTRO_TAC `n:num` `read (memory :> bytes(pk,768))` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `pk:int64`; `n:num`; `guard:int64`; `pc:num`;
    `stackpointer:int64`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
  SIMP_TAC[]);;
