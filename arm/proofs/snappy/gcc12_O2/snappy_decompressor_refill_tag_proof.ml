(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_refill_tag_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* CalculateNeeded as the code computes it (cmp/ccmp/csel on the tag byte),  *)
(* checked on all 256 bytes.                                                 *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_TAG_NEEDED_CODE = prove
 (`!c:byte.
    (if ~(if &(val(word_zx c:int32)) - &239:int =
             &(val(word_sub (word_zx c:int32) (word 239))) /\
             ~(val(word_sub (word_zx c:int32) (word 239)) = 0)
          then val(word_sub (word_and (word_zx c:int32) (word 3)) (word 0)) = 0
          else F)
     then word_zx(word_and (word_jshr (word 84083201:int32)
                              (word_shl (word_subword c (0,2):int32) 3))
                           (word 255)):int64
     else word_zx(word_sub (word_ushr (word_zx c:int32) 2) (word 58)):int64) =
    word(snappy_tag_needed c)`,
  GEN_TAC THEN REWRITE_TAC[snappy_tag_needed] THEN
  SUBGOAL_THEN `c:byte = word(val c)` (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [REWRITE_TAC[WORD_VAL]; ALL_TAC] THEN
  MP_TAC(ISPEC `c:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`val(c:byte)`,`v:num`) THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV ORELSEC
                      INT_RED_CONV)) THEN
  REWRITE_TAC[]);;

let VAL_WORD_SNAPPY_TAG_NEEDED = prove
 (`!c. val(word(snappy_tag_needed c):int64) = snappy_tag_needed c`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD_EQ_EQ; DIMINDEX_64] THEN
  MP_TAC(SPEC `c:byte` SNAPPY_TAG_NEEDED_BOUNDS) THEN ARITH_TAC);;

let WORD_SUB_ADD_LEFT = prove
 (`!x y:int64. word_sub (word_add x y) x = y`,
  CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* The proofs: bstep with the branches split (ARM_BSTEP_RUN_GEN_TAC), the     *)
(* cases r = n - k = 0, 1, 2, 3, 4 (with the tag short or not) and r >= 5    *)
(* split first, so that the lengths of memmove and of the scratch bytes are  *)
(* numerals.                                                                 *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_REFILL_TAG_NORM_TAC (ths:thm list) : tactic =
  RULE_ASSUM_TAC(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),_)),_)
        when c <> `events:(armstate,(uarch_event)list)component` ->
        (try CONV_RULE(RAND_CONV(REWRITE_CONV ths)) th with Failure _ -> th)
    | _ -> th);;

let SNAPPY_REFILL_TAG_MEMMOVE_TAC exec rest =
  fun i ->
    (ELF_RELOCATED_DATA_TAC ~defs:[snappy_libsnappy_gcc12_O2_relocated]
       ~select:(elf_slots_importing ["memmove"]) THEN
     USE_THEN "H_MEMMOVE" (fun th ->
      ARM_BSTEP_PLT_STUB_TAC exec THEN
      ARM_BSTEP_CONTRACT_TAC exec th
       [`read events s`; `read X0 s`; `read X1 s`; `read X2 s`;
        mk_comb(`num_of_bytelist:byte list->num`,rest); `read X30 s`]
       ("s" ^ string_of_int (i + 4))) THEN
     MEMACCESS_INBOUNDS_TO_INSET_TAC),5;;

let SNAPPY_REFILL_TAG_CASE_TAC tm =
  FIRST_X_ASSUM(fun c ->
    if concl c = tm then RULE_ASSUM_TAC(REWRITE_RULE[c]) THEN ASSUME_TAC c
    else NO_TAC);;

let SNAPPY_REFILL_TAG_LEAF_TAC : tactic =
  BSTEP_FINAL_TAC THEN
  ASM_REWRITE_TAC[snappy_refill_ok; BITVAL_CLAUSES; NOT_CONS_NIL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(CONV_TAC WORD_REDUCE_CONV THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(REWRITE_TAC[READ_COMPONENT_COMPOSE; bytelist_clauses] THEN NO_TAC) THEN
  TRY(ASM_REWRITE_TAC[READ_BYTELIST_EQ_BYTES] THEN NO_TAC) THEN
  MEMACCESS_INSET_TAC;;

let SNAPPY_DECOMPRESSOR_REFILL_TAG_EMPTY_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (SNAPPY_DECOMPRESSOR_REFILL_TAG_EMPTY_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  let exec = SNAPPY_DECOMPRESSOR_REFILL_TAG_GCC12_O2_EXEC in
  let rest = `rest:byte list` in
  let calls = [mk_comb(`word:num->int64`,
                       mk_binop `(+):num->num->num` `pc:num`
                         (mk_small_numeral(layout "plt_memmove"))),
               SNAPPY_REFILL_TAG_MEMMOVE_TAC exec rest] in
  let num r = mk_small_numeral r in
  let rcase ro =
    (match ro with
       Some r ->
         let nk = REWRITE_RULE[ASSUME (subst [num r,`r:num`] `n - k = r`)]
                    (ASSUME `word_sub (word n) (word k):int64 = word(n - k)`)
         and ad = REWRITE_RULE[ASSUME (subst [num r,`r:num`] `n - k = r`)]
                    (ASSUME `word_add (word_add p (word k)) (word(n - k)):int64 =
                             word_add p (word n)`)
         and wsr = WORD_RULE
                    `word_sub (word_add p (word n)) (word_add p (word k)):int64 =
                     word_sub (word n) (word k)` in
         let wsr = TRANS wsr nk
         and d41 = WORD_RULE (subst [num r,`r:num`; num(41+r),`t:num`]
                    `word_add (word_add d (word 41)) (word r):int64 =
                     word_add d (word t)`) in
         let norm = SNAPPY_REFILL_TAG_NORM_TAC
                      (if r = 0 then [WORD_SUB_REFL; WORD_SUB_ADD_LEFT;
                                      SNAPPY_TAG_NEEDED_CODE]
                       else [nk; wsr; ad; d41; WORD_SUB_ADD_LEFT;
                             SNAPPY_TAG_NEEDED_CODE]) in
         let kill = BSTEP_ARITH_KILL_TAC
                      [VAL_WORD_SNAPPY_TAG_NEEDED; VAL_WORD_0] in
         (if r = 0 then
            SUBGOAL_THEN `n:num = k` SUBST_ALL_TAC THENL
             [ASM_ARITH_TAC; ALL_TAC] THEN
            REWRITE_TAC[SUB_REFL] THEN RULE_ASSUM_TAC(REWRITE_RULE[SUB_REFL]) THEN
            ENSURES_INIT_TAC "s0"
          else
            ENSURES_INIT_TAC "s0" THEN
            SNAPPY_REFILL_TAG_CASE_TAC (subst [num r,`r:num`] `n - k = r`)) THEN
         (if r = 0 then
            SUBGOAL_THEN `rest:byte list = []` SUBST_ALL_TAC THENL
             [ASM_REWRITE_TAC[GSYM LENGTH_EQ_NIL]; ALL_TAC]
          else
            SUBGOAL_THEN `~(rest:byte list = [])` ASSUME_TAC THENL
             [ASM_REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ARITH_TAC; ALL_TAC] THEN
            FIRST_ASSUM(fun th ->
              if can (term_match [] `read (memory :> bytelist(a,m)) s = rest`)
                     (concl th) then
                let th' = REWRITE_RULE[GSYM(ASSUME (subst [num r,`r:num`]
                            `LENGTH(rest:byte list) = r`))] th in
                ASSUME_TAC(REWRITE_RULE[WORD_ADD_0; EL]
                  (MATCH_MP READ_MEMORY_BYTELIST_EL
                    (CONJ th' (MP (ARITH_RULE (subst [num r,`r:num`]
                        `LENGTH(rest:byte list) = r ==> 0 < LENGTH rest`))
                       (ASSUME (subst [num r,`r:num`]
                        `LENGTH(rest:byte list) = r`)))))) THEN
                ASSUME_TAC(CONJUNCT2(EQ_MP (PART_MATCH lhs READ_BYTELIST_EQ_BYTES (concl th)) th))
              else NO_TAC)) THEN
         ELF_RELOCATED_DATA_TAC ~defs:[snappy_libsnappy_gcc12_O2_relocated]
           ~select:(elf_slots_at [0x1fc98; 0x1fca0]) THEN
         ELF_RELOCATED_DATA_TAC ~defs:[snappy_libsnappy_gcc12_O2_relocated]
           ~select:(elf_slots_importing ["memmove"]) THEN
         ARM_BSTEP_RUN_GEN_TAC ~kill ~norm ~calls exec 1 SNAPPY_REFILL_TAG_LEAF_TAC
     | None ->
         let norm = SNAPPY_REFILL_TAG_NORM_TAC
           [ASSUME `word_sub (word n) (word k):int64 = word(n - k)`;
            TRANS (WORD_RULE
              `word_sub (word_add p (word n)) (word_add p (word k)):int64 =
               word_sub (word n) (word k)`)
             (ASSUME `word_sub (word n) (word k):int64 = word(n - k)`);
            ASSUME `word_add (word_add p (word k)) (word(n - k)):int64 =
                    word_add p (word n)`;
            WORD_SUB_ADD_LEFT; SNAPPY_TAG_NEEDED_CODE] in
         let kill = BSTEP_ARITH_KILL_TAC
           [VAL_WORD_SNAPPY_TAG_NEEDED; VAL_WORD_0;
            TRANS (WORD_RULE
              `word_sub (word_add p (word n)) (word_add p (word k)):int64 =
               word_sub (word n) (word k)`)
             (ASSUME `word_sub (word n) (word k):int64 = word(n - k)`);
            ASSUME `word_sub (word n) (word k):int64 = word(n - k)`;
            ASSUME `val(word(n - k):int64) = n - k`] in
         SUBGOAL_THEN `val(word(n - k):int64) = n - k` ASSUME_TAC THENL
          [REWRITE_TAC[VAL_WORD_EQ_EQ; DIMINDEX_64] THEN ASM_ARITH_TAC;
           ALL_TAC] THEN
         SUBGOAL_THEN `~(rest:byte list = [])` ASSUME_TAC THENL
          [ASM_REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
         ENSURES_INIT_TAC "s0" THEN
         FIRST_ASSUM(fun th ->
           if can (term_match [] `read (memory :> bytelist(a,m)) s = rest`)
                  (concl th) then
             let th' = REWRITE_RULE[GSYM(ASSUME `LENGTH(rest:byte list) = n - k`)] th in
             ASSUME_TAC(REWRITE_RULE[WORD_ADD_0; EL]
               (MATCH_MP READ_MEMORY_BYTELIST_EL
                 (CONJ th' (MP (ARITH_RULE
                    `5 <= n - k /\ LENGTH(rest:byte list) = n - k ==> 0 < LENGTH rest`)
                    (CONJ (ASSUME `5 <= n - k`)
                          (ASSUME `LENGTH(rest:byte list) = n - k`))))))
           else NO_TAC) THEN
         ELF_RELOCATED_DATA_TAC ~defs:[snappy_libsnappy_gcc12_O2_relocated]
           ~select:(elf_slots_at [0x1fc98; 0x1fca0]) THEN
         ARM_BSTEP_RUN_GEN_TAC ~kill ~norm exec 1 SNAPPY_REFILL_TAG_LEAF_TAC) in
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; ALL] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (LABEL_TAC "H_MEMMOVE" o REWRITE_RULE[memmove_correct_safe_contract])
    STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `word_sub (word n) (word k):int64 = word(n - k)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WORD_SUB]; ALL_TAC] THEN
  SUBGOAL_THEN `word_add (word_add p (word k)) (word(n - k)):int64 =
                word_add p (word n)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `HD(rest:byte list)` SNAPPY_TAG_NEEDED_BOUNDS) THEN STRIP_TAC THEN
  ASM_CASES_TAC `n - k = 0` THENL [rcase (Some 0); ALL_TAC] THEN
  MAP_EVERY (fun r ->
    ASM_CASES_TAC (subst [num r,`r:num`] `n - k = r`) THENL
     [ASM_CASES_TAC (subst [num r,`r:num`] `snappy_tag_needed(HD(rest:byte list)) <= r`)
      THEN rcase (Some r);
      ALL_TAC]) [1;2;3;4] THEN
  SUBGOAL_THEN `5 <= n - k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `snappy_tag_needed(HD(rest:byte list)) <= n - k` ASSUME_TAC
  THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(n - k < 5)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `memrange(word_add p (word k):int64,1) SUBSET
                memrange(word_add p (word k),n - k)` ASSUME_TAC THENL
   [MATCH_MP_TAC MEMRANGE_PREFIX_SUBSET THEN ASM_ARITH_TAC; ALL_TAC] THEN
  rcase None);;

let SNAPPY_DECOMPRESSOR_REFILL_TAG_WINDOW_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (SNAPPY_DECOMPRESSOR_REFILL_TAG_WINDOW_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  let exec = SNAPPY_DECOMPRESSOR_REFILL_TAG_GCC12_O2_EXEC in
  let calls = [mk_comb(`word:num->int64`,
                       mk_binop `(+):num->num->num` `pc:num`
                         (mk_small_numeral(layout "plt_memmove"))),
               SNAPPY_REFILL_TAG_MEMMOVE_TAC exec `w:byte list`] in
  let num r = mk_small_numeral r in
  let byte_facts =
    FIRST_ASSUM(fun th ->
      if can (term_match [] `read (memory :> bytelist(a,LENGTH w)) s = w`)
             (concl th) then
        ASSUME_TAC(REWRITE_RULE[WORD_ADD_0; EL]
          (MATCH_MP READ_MEMORY_BYTELIST_EL
            (CONJ th (MP (ARITH_RULE `~(LENGTH(w:byte list) = 0) ==> 0 < LENGTH w`)
                         (ASSUME `~(LENGTH(w:byte list) = 0)`))))) THEN
        ASSUME_TAC(CONJUNCT2(EQ_MP (PART_MATCH lhs READ_BYTELIST_EQ_BYTES (concl th)) th))
      else NO_TAC) in
  let slots =
    ELF_RELOCATED_DATA_TAC ~defs:[snappy_libsnappy_gcc12_O2_relocated]
      ~select:(elf_slots_at [0x1fc98; 0x1fca0]) THEN
    ELF_RELOCATED_DATA_TAC ~defs:[snappy_libsnappy_gcc12_O2_relocated]
      ~select:(elf_slots_importing ["memmove"]) in
  let rcase ro =
    match ro with
      Some r ->
        let d41 = WORD_RULE (subst [num r,`r:num`; num(41+r),`t:num`]
                   `word_add (word_add d (word 41)) (word r):int64 =
                    word_add d (word t)`) in
        let norm = SNAPPY_REFILL_TAG_NORM_TAC
                     [d41; WORD_SUB_ADD_LEFT; WORD_SUB_REFL;
                      SNAPPY_TAG_NEEDED_CODE] in
        let kill = BSTEP_ARITH_KILL_TAC
                     [VAL_WORD_SNAPPY_TAG_NEEDED; VAL_WORD_0; WORD_SUB_ADD_LEFT] in
        ENSURES_INIT_TAC "s0" THEN byte_facts THEN
        SNAPPY_REFILL_TAG_CASE_TAC (subst [num r,`r:num`]
                                       `LENGTH(w:byte list) = r`) THEN
        slots THEN
        ARM_BSTEP_RUN_GEN_TAC ~kill ~norm ~calls exec 1 SNAPPY_REFILL_TAG_LEAF_TAC
    | None ->
        let norm = SNAPPY_REFILL_TAG_NORM_TAC
                     [WORD_SUB_ADD_LEFT; WORD_SUB_REFL; SNAPPY_TAG_NEEDED_CODE] in
        let kill = BSTEP_ARITH_KILL_TAC
                     [VAL_WORD_SNAPPY_TAG_NEEDED; VAL_WORD_0; WORD_SUB_ADD_LEFT;
                      ASSUME `val(word(LENGTH(w:byte list)):int64) = LENGTH w`] in
        SUBGOAL_THEN `val(word(LENGTH(w:byte list)):int64) = LENGTH w`
          ASSUME_TAC THENL
         [REWRITE_TAC[VAL_WORD_EQ_EQ; DIMINDEX_64] THEN ASM_ARITH_TAC;
          ALL_TAC] THEN
        ENSURES_INIT_TAC "s0" THEN byte_facts THEN slots THEN
        ARM_BSTEP_RUN_GEN_TAC ~kill ~norm exec 1 SNAPPY_REFILL_TAG_LEAF_TAC in
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; ALL] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (LABEL_TAC "H_MEMMOVE" o REWRITE_RULE[memmove_correct_safe_contract])
    STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(LENGTH(w:byte list) = 0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
  MP_TAC(SPEC `HD(w:byte list)` SNAPPY_TAG_NEEDED_BOUNDS) THEN STRIP_TAC THEN
  MAP_EVERY (fun r ->
    ASM_CASES_TAC (subst [num r,`r:num`] `LENGTH(w:byte list) = r`) THENL
     [ASM_CASES_TAC (subst [num r,`r:num`] `snappy_tag_needed(HD(w:byte list)) <= r`)
      THEN rcase (Some r);
      ALL_TAC]) [1;2;3;4] THEN
  SUBGOAL_THEN `5 <= LENGTH(w:byte list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `snappy_tag_needed(HD(w:byte list)) <= LENGTH w` ASSUME_TAC
  THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(LENGTH(w:byte list) < 5)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `memrange(ip:int64,1) SUBSET memrange(ip,LENGTH(w:byte list))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MEMRANGE_PREFIX_SUBSET THEN ASM_ARITH_TAC; ALL_TAC] THEN
  rcase None);;
