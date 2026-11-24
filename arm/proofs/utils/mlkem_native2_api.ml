(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of the API functions of mlkem_native2 for the three  *)
(* parameter sets (the proof files of arm/proofs/mlkem_native/asm for k = 2, *)
(* 3, 4): the tables of the constants block in the image, the use of the     *)
(* contracts of the functions they call, and the proofs that are the same    *)
(* for the three sets up to the sizes.                                       *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/asm/layout.ml";;
needs "arm/proofs/mlkem_native/asm/hash_h_spec.ml";;
needs "arm/proofs/mlkem_native/asm/check_encoding_spec.ml";;
needs "arm/proofs/utils/mlkem_native2_sponge.ml";;
needs "arm/proofs/utils/mlkem_native2_safety.ml";;

(* ------------------------------------------------------------------------- *)
(* The tables of the constants block, at mlkem_native2_constants in the      *)
(* image: MLKEM_NATIVE2_IMAGE_DATA name off len defines name as the len      *)
(* bytes of the image at off and gives                                       *)
(*                                                                           *)
(* |- !s pc. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc         *)
(*           ==> bytes_loaded s (word(pc + off)) name                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE2_IMAGE_DATA name off len =
  let l = dest_list(rand(concl mlkem_native2_image_mc)) in
  let data = mk_list(fst(chop_list len (snd(chop_list off l))),`:byte`) in
  let def = new_definition(mk_eq(mk_var(name,`:byte list`),data)) in
  def,MLKEM_NATIVE_IMAGE_DATA_RULE_FOR mlkem_native2_image_mc def off;;

(*** The Keccak round constants, at offset MLKEM_C_RC = 0 ***)

let mlkem_native2_rc_data,MLKEM_NATIVE2_RC_DATA_LOADED =
  MLKEM_NATIVE2_IMAGE_DATA "mlkem_native2_rc_data"
   (layout "mlkem_native2_constants") 192;;

let MLKEM_NATIVE2_RC_DATA = prove
 (`num_of_bytelist mlkem_native2_rc_data = num_of_wordlist round_constants`,
  REWRITE_TAC[mlkem_native2_rc_data; round_constants] THEN
  REWRITE_TAC[num_of_bytelist; num_of_wordlist] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV);;

let MLKEM_NATIVE2_ROUND_CONSTANTS = prove
 (`!s pc. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc
          ==> wordlist_from_memory(word(pc + mlkem_native2_constants),24) s =
              round_constants`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP MLKEM_NATIVE2_RC_DATA_LOADED) THEN
  REWRITE_TAC[WORDLIST_FROM_MEMORY_ROUND_CONSTANTS] THEN
  REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES; MLKEM_NATIVE2_RC_DATA;
              CONV_RULE(RAND_CONV LENGTH_CONV)
               (AP_TERM `LENGTH:byte list->num` mlkem_native2_rc_data)] THEN
  SIMP_TAC[]);;

(*** The correctness of mlkem_check_encoding for k = 2, 3 or 4 ***)

let MLKEM_CHECK_ENCODING_K_RULE k =
  let th1 = SPECL [`a:int64`; mk_comb(`word:num->int64`,mk_small_numeral k)]
                  MLKEM_CHECK_ENCODING_SUBROUTINE_CORRECT in
  let th2 = CONV_RULE(ONCE_DEPTH_CONV WORD_NUM_RED_CONV THENC
                      ONCE_DEPTH_CONV NUM_MULT_CONV) th1 in
  GEN `a:int64`
   (REWRITE_RULE[ARITH_RULE `2 < 2 EXP 61 /\ 3 < 2 EXP 61 /\ 4 < 2 EXP 61`;
                 ARITH_RULE `4096 = 2 EXP 12`] th2);;

(* ------------------------------------------------------------------------- *)
(* The comparison of two 32-byte strings by their four 64-bit words.         *)
(* ------------------------------------------------------------------------- *)

let NUM_EQ_BIGDIGITS = prove
 (`!x y k. x < 2 EXP (64 * k) /\ y < 2 EXP (64 * k)
           ==> (x = y <=> !j. j < k ==> bigdigit x j = bigdigit y j)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL [SIMP_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`x:num`; `k:num`] BIGDIGITSUM_WORKS) THEN
  MP_TAC(SPECL [`y:num`; `k:num`] BIGDIGITSUM_WORKS) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
  MATCH_MP_TAC NSUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM]);;

let WORD_OR_XOR_DIGITS_EQ_0 = prove
 (`!x y. x < 2 EXP 256 /\ y < 2 EXP 256
         ==> (val(word_or
                   (word_or
                     (word_xor (word(bigdigit x 0)) (word(bigdigit y 0)))
                     (word_xor (word(bigdigit x 1)) (word(bigdigit y 1))))
                   (word_or
                     (word_xor (word(bigdigit x 2)) (word(bigdigit y 2)))
                     (word_xor (word(bigdigit x 3))
                               (word(bigdigit y 3)))):int64) = 0 <=>
              x = y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:num`; `y:num`; `4`] NUM_EQ_BIGDIGITS) THEN
  ASM_REWRITE_TAC[ARITH_RULE `64 * 4 = 256`] THEN DISCH_THEN SUBST1_TAC THEN
  CONV_TAC(RAND_CONV EXPAND_CASES_CONV) THEN
  REWRITE_TAC[VAL_EQ_0; WORD_OR_EQ_0; WORD_XOR_EQ_0] THEN
  REWRITE_TAC[WORD_EQ; DIMINDEX_64; CONG] THEN
  SIMP_TAC[bigdigit; MOD_MOD_REFL; CONJ_ASSOC]);;

let READ_MEMORY_BYTES64_BIGDIGIT = prove
 (`!a:int64 m n j s:armstate.
        read (memory :> bytes(a,m)) s = n /\ 8 * j + 8 <= m
        ==> read (memory :> bytes64(word_add a (word(8 * j)))) s =
            word(bigdigit n j)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[bigdigit; ARITH_RULE `64 * j = 8 * 8 * j`] THEN
  MATCH_MP_TAC READ_MEMORY_BYTES64_OF_NUM THEN EXISTS_TAC `m:num` THEN
  ASM_REWRITE_TAC[]);;

(*** The four words of a 32-byte string n at a in state s ***)

let BIGDIGITS_32_TAC a n s =
  MAP_EVERY (fun j ->
    MP_TAC(SPECL [a; `32`; n; mk_small_numeral j; s]
      READ_MEMORY_BYTES64_BIGDIGIT) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC) (0--3);;

(* ------------------------------------------------------------------------- *)
(* Bounds in the memory accesses of the events of a callee given with        *)
(* arithmetic on numerals, evaluated for the discharge of memaccess_inbounds *)
(* ------------------------------------------------------------------------- *)

let MEMACCESS_NUMERALS_TAC =
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_comb c && is_const(fst(strip_comb c)) &&
       name_of(fst(strip_comb c)) = "memaccess_inbounds"
    then CONV_RULE(DEPTH_CONV WORD_NUM_RED_CONV) th else th);;

(* ------------------------------------------------------------------------- *)
(* The proofs of check_pk, the modulus check of the k polynomials of the     *)
(* encapsulation key with mlkem_check_encoding, and check_sk, the hash check *)
(* of the decapsulation key with mlkem_hash_h, for the code exec of the      *)
(* function in the image: in check_sk, ek is at offset ekoff of sk and the   *)
(* hash at offset hoff.                                                      *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE2_CHECK_PK_CORRECT_TAC exec k =
  let ceth = MLKEM_CHECK_ENCODING_K_RULE k in
  MAP_EVERY X_GEN_TAC [`pk:int64`; `n:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 16 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x29_init" `X29` THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC exec (1--4) THEN
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native2_image_mc,exec,layout "mlkem_check_encoding",
    mlkem_check_encoding_mc,ceth)
   [`read X0 s`; `n:num`; `pc + mlkem_check_encoding`; `read X30 s`] 5 THEN
  ARM_STEPS_TAC exec (6--10) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `4096 = 2 EXP 12`] THEN
  W(fun (_,w) -> SPEC_TAC(find_term is_forall w,`b:bool`)) THEN
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  REPEAT(CHANGED_TAC
   (CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN REWRITE_TAC[]));;

let MLKEM_NATIVE2_CHECK_PK_SAFE_TAC exec =
  ASSUME_CALLEE_SAFETY_TAILED_TAC MLKEM_CHECK_ENCODING_SUBROUTINE_SAFE_FRAMED
    "H_CE" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x29_init" `X29` THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC exec (1--4) THEN
  REMOVE_THEN "H_CE" (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native2_image_mc,exec,
       layout "mlkem_check_encoding",mlkem_check_encoding_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`;
       `pc + mlkem_check_encoding`; `read X30 s`] 5 THENL
     [EXISTS_E2_TAC (ref [`pk:int64`; `pc:num`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC "H_CE" safety_th]) THEN
  ARM_STEPS_TAC exec (6--10) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MEMACCESS_NUMERALS_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE2_CHECK_SK_CORRECT_TAC exec hoff =
  MAP_EVERY X_GEN_TAC
   [`sk:int64`; `ek:byte list`; `h:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 448 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** The hash of ek, with the round constants in the image ***)

  ARM_STEPS_TAC exec (1--8) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC exec (9--10) THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[WORD_ADD] o
    MATCH_MP MLKEM_NATIVE2_ROUND_CONSTANTS) THEN
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native2_image_mc,exec,0,
    mlkem_native2_image_mc,MLKEM_NATIVE_HASH_H_ASM_IMAGE_SUBROUTINE_CORRECT)
   [`read X0 s`; `read X1 s`; `ek:byte list`; `read X3 s`; `pc:num`;
    `read SP s`; `read X30 s`] 11 THEN

  (*** The comparison with h, word by word ***)

  BIGDIGITS_32_TAC `word_add stackpointer (word 416):int64`
   `num_of_bytelist(sha3_256 ek)` `s11:armstate` THEN
  BIGDIGITS_32_TAC (mk_comb(`word_add (sk:int64)`,
                            mk_comb(`word:num->int64`,mk_small_numeral hoff)))
   `h:num` `s11:armstate` THEN
  ARM_STEPS_TAC exec (12--30) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_SUB_0] THEN
  W(fun (_,w) ->
    MP_TAC(PART_MATCH (lhand o rand) WORD_OR_XOR_DIGITS_EQ_0
            (find_term (can (term_match [] `val(x:int64) = 0`)) w))) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPEC `sha3_256 ek` NUM_OF_BYTELIST_BOUND) THEN
      REWRITE_TAC[sha3_256; LENGTH_LIST_OF_SEQ] THEN
      CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (can (term_match
       [`sk:int64`; `h:num`]
       (mk_eq(mk_comb(`read (memory :> bytes (word_add sk (word k),32))`,
                      `s:armstate`),`h:num`))) o concl)) THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; ARITH_RULE `256 = 8 * 32`;
                  READ_BYTES_BOUND]];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[EQ_SYM_EQ] THEN COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV;;

let MLKEM_NATIVE2_CHECK_SK_SAFE_TAC exec eklen =
  ASSUME_CALLEE_SAFETY_TAILED_TAC MLKEM_NATIVE_HASH_H_ASM_IMAGE_SUBROUTINE_SAFE "H_HASH" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC exec (1--8) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC exec (9--10) THEN
  REMOVE_THEN "H_HASH" (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native2_image_mc,exec,0,mlkem_native2_image_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`;
       mk_small_numeral eklen; `read X3 s`; `pc:num`; `read SP s`;
       `read X30 s`] 11 THENL
     [EXISTS_E2_TAC (ref [`sk:int64`; `pc:num`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC "H_HASH" safety_th]) THEN
  ARM_STEPS_TAC exec (12--30) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MEMACCESS_NUMERALS_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;
