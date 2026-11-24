(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of the API functions of the x86 mlkem_native2 for    *)
(* the three parameter sets (x86/proofs/mlkem_native/asm/mlkem512.ml,        *)
(* mlkem768.ml and mlkem1024.ml): the tables of the constants block in the   *)
(* image, the theorems for the functions they call in the form a caller      *)
(* needs, and the proofs of the key checks, which are the same for the three *)
(* sets up to the sizes. As arm/proofs/utils/mlkem_native2_api.ml for        *)
(* AArch64.                                                                  *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/asm/layout.ml";;
needs "x86/proofs/utils/mlkem_native2_safety.ml";;
needs "x86/proofs/utils/mlkem_compress_consts.ml";;
needs "x86/proofs/mlkem_native/asm/ntt_x86_spec.ml";;
needs "x86/proofs/mlkem_native/asm/rej_uniform_alt_VARIABLE_TIME_spec.ml";;
needs "x86/proofs/mlkem_native/asm/hash_h_spec.ml";;
needs "x86/proofs/mlkem_native/asm/check_encoding_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The tables of the constants block mlkem_native2_constants in the image:   *)
(* api_table name off len defines name as the len bytes of the block at off  *)
(* and proves                                                                *)
(*                                                                           *)
(* |- !s pc. bytes_loaded s (word pc) mlkem_native2_image_mc                 *)
(*           ==> read (memory :> bytes(word(pc + N),len)) s =                *)
(*               num_of_bytelist name                                        *)
(*                                                                           *)
(* with N = mlkem_native2_constants + off as a numeral.                      *)
(* ------------------------------------------------------------------------- *)

let api_table name off len =
  let n = layout "mlkem_native2_constants" + off in
  let def,loaded = x86_image_data mlkem_native2_image_mc name n len in
  let lenth = CONV_RULE(RAND_CONV LENGTH_CONV)
                (AP_TERM `LENGTH:byte list->num` def) in
  let tm = vsubst [mk_small_numeral n,`n:num`; mk_small_numeral len,`len:num`;
                   lhs(concl def),`l:byte list`]
   `!s pc. bytes_loaded s (word pc) mlkem_native2_image_mc
           ==> read (memory :> bytes(word(pc + n),len)) s =
               num_of_bytelist l` in
  def,prove(tm,
    REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP loaded) THEN
    REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES; lenth]);;

let mlkem_native2_rc_table,MLKEM_NATIVE2_RC_TABLE =
  api_table "mlkem_native2_rc_table" 0 192;;

let MLKEM_NATIVE2_RC_TABLE_VALUE_STMT =
  `num_of_bytelist mlkem_native2_rc_table = num_of_wordlist round_constants`;;

let MLKEM_NATIVE2_RC_TABLE_VALUE = assume_spec MLKEM_NATIVE2_RC_TABLE_VALUE_STMT;;

(*** The other tables, and their values as the lists the callees take ***)

let mlkem_native2_rho8_table,MLKEM_NATIVE2_RHO8_TABLE =
  api_table "mlkem_native2_rho8_table" 192 32;;
let mlkem_native2_rho56_table,MLKEM_NATIVE2_RHO56_TABLE =
  api_table "mlkem_native2_rho56_table" 224 32;;
let mlkem_native2_qdata_table,MLKEM_NATIVE2_QDATA_TABLE =
  api_table "mlkem_native2_qdata_table" 256 1248;;

(* The address of the qdata table, as a name for the terms below             *)

install_layout ["mlkem_native2_qdata",layout "mlkem_native2_constants" + 256];;
let mlkem_native2_compress_d4_table,MLKEM_NATIVE2_COMPRESS_D4_TABLE =
  api_table "mlkem_native2_compress_d4_table" 1504 32;;
let mlkem_native2_decompress_d4_table,MLKEM_NATIVE2_DECOMPRESS_D4_TABLE =
  api_table "mlkem_native2_decompress_d4_table" 1536 32;;
let mlkem_native2_compress_d5_table,MLKEM_NATIVE2_COMPRESS_D5_TABLE =
  api_table "mlkem_native2_compress_d5_table" 1568 32;;
let mlkem_native2_decompress_d5_table,MLKEM_NATIVE2_DECOMPRESS_D5_TABLE =
  api_table "mlkem_native2_decompress_d5_table" 1600 96;;
let mlkem_native2_compress_d10_table,MLKEM_NATIVE2_COMPRESS_D10_TABLE =
  api_table "mlkem_native2_compress_d10_table" 1696 32;;
let mlkem_native2_decompress_d10_table,MLKEM_NATIVE2_DECOMPRESS_D10_TABLE =
  api_table "mlkem_native2_decompress_d10_table" 1728 32;;
let mlkem_native2_compress_d11_table,MLKEM_NATIVE2_COMPRESS_D11_TABLE =
  api_table "mlkem_native2_compress_d11_table" 1760 64;;
let mlkem_native2_decompress_d11_table,MLKEM_NATIVE2_DECOMPRESS_D11_TABLE =
  api_table "mlkem_native2_decompress_d11_table" 1824 128;;
let mlkem_native2_rej_table,MLKEM_NATIVE2_REJ_TABLE =
  api_table "mlkem_native2_rej_table" 1952 4096;;

let API_TABLE_VALUE_TAC defs =
  REWRITE_TAC defs THEN REWRITE_TAC[MAP; num_of_bytelist; num_of_wordlist] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  REWRITE_TAC[DIMINDEX_8; DIMINDEX_16; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV;;

let MLKEM_NATIVE2_RHO8_TABLE_VALUE_STMT =
  `num_of_bytelist mlkem_native2_rho8_table = num_of_wordlist rho8_constant`;;

let MLKEM_NATIVE2_RHO8_TABLE_VALUE = assume_spec MLKEM_NATIVE2_RHO8_TABLE_VALUE_STMT;;

let MLKEM_NATIVE2_RHO56_TABLE_VALUE_STMT =
  `num_of_bytelist mlkem_native2_rho56_table = num_of_wordlist rho56_constant`;;

let MLKEM_NATIVE2_RHO56_TABLE_VALUE = assume_spec MLKEM_NATIVE2_RHO56_TABLE_VALUE_STMT;;

let MLKEM_NATIVE2_QDATA_TABLE_VALUE_STMT =
  `num_of_bytelist mlkem_native2_qdata_table =
   num_of_wordlist(MAP (iword:int->int16) qdata_full)`;;

let MLKEM_NATIVE2_QDATA_TABLE_VALUE = assume_spec MLKEM_NATIVE2_QDATA_TABLE_VALUE_STMT;;

let MLKEM_NATIVE2_COMPRESS_D4_TABLE_VALUE_STMT =
  `num_of_bytelist mlkem_native2_compress_d4_table =
   num_of_wordlist((MAP iword compress_d4_data):(8 word) list)`;;

let MLKEM_NATIVE2_COMPRESS_D4_TABLE_VALUE = assume_spec MLKEM_NATIVE2_COMPRESS_D4_TABLE_VALUE_STMT;;

let NUM_OF_BYTELIST_WORDLIST_STMT =
  `!l:byte list. num_of_bytelist l = num_of_wordlist l`;;

let NUM_OF_BYTELIST_WORDLIST = assume_spec NUM_OF_BYTELIST_WORDLIST_STMT;;

let MLKEM_NATIVE2_REJ_TABLE_DATA_STMT =
  `mlkem_native2_rej_table = mlkem_rej_uniform_table`;;

let MLKEM_NATIVE2_REJ_TABLE_DATA = assume_spec MLKEM_NATIVE2_REJ_TABLE_DATA_STMT;;

let MLKEM_NATIVE2_REJ_TABLE_VALUE_STMT =
  `num_of_bytelist mlkem_native2_rej_table =
   num_of_wordlist mlkem_rej_uniform_table`;;

let MLKEM_NATIVE2_REJ_TABLE_VALUE = assume_spec MLKEM_NATIVE2_REJ_TABLE_VALUE_STMT;;

(* ------------------------------------------------------------------------- *)
(* The constant-time and memory safety of mlkem_check_encoding with the      *)
(* frame of its correctness theorem, as needed to use it as a callee (that   *)
(* in its proof file is for the library, with a trivial frame), and its      *)
(* correctness for a given number k of polynomials.                          *)
(* ------------------------------------------------------------------------- *)

let MLKEM_CHECK_ENCODING_NOIBT_SUBROUTINE_SAFE_FRAMED_STMT =
  `exists f_events.
    forall e a k pc stackpointer returnaddress.
        ensures x86
        (\s. bytes_loaded s (word pc) mlkem_check_encoding_tmc /\
             read RIP s = word pc /\
             read RSP s = stackpointer /\
             read (memory :> bytes64 stackpointer) s = returnaddress /\
             C_ARGUMENTS [a; k] s /\
             read events s = e)
        (\s. read RIP s = returnaddress /\
             read RSP s = word_add stackpointer (word 8) /\
             (exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_events a k pc stackpointer returnaddress /\
                  memaccess_inbounds e2
                    [a,(384 * val k) * 1; stackpointer,8]
                    [stackpointer,8]))
        (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`;;

let MLKEM_CHECK_ENCODING_NOIBT_SUBROUTINE_SAFE_FRAMED = assume_spec MLKEM_CHECK_ENCODING_NOIBT_SUBROUTINE_SAFE_FRAMED_STMT;;

let MLKEM_CHECK_ENCODING_SUBROUTINE_SAFE_FRAMED =
  ADD_IBT_RULE MLKEM_CHECK_ENCODING_NOIBT_SUBROUTINE_SAFE_FRAMED;;

let MLKEM_CHECK_ENCODING_K_RULE k =
  let th1 = SPECL [`a:int64`; mk_comb(`word:num->int64`,mk_small_numeral k)]
                  MLKEM_CHECK_ENCODING_SUBROUTINE_CORRECT in
  let th2 = CONV_RULE(ONCE_DEPTH_CONV WORD_NUM_RED_CONV THENC
                      ONCE_DEPTH_CONV NUM_MULT_CONV) th1 in
  GEN `a:int64` (REWRITE_RULE[ARITH_RULE `4096 = 2 EXP 12`] th2);;

(* ------------------------------------------------------------------------- *)
(* The comparison of two 32-byte strings by their four 64-bit words.         *)
(* ------------------------------------------------------------------------- *)

let NUM_EQ_BIGDIGITS_STMT =
  `!x y k. x < 2 EXP (64 * k) /\ y < 2 EXP (64 * k)
           ==> (x = y <=> !j. j < k ==> bigdigit x j = bigdigit y j)`;;

let NUM_EQ_BIGDIGITS = assume_spec NUM_EQ_BIGDIGITS_STMT;;

let WORD_OR_XOR_DIGITS_EQ_0_STMT =
  `!x y. x < 2 EXP 256 /\ y < 2 EXP 256
         ==> (val(word_or
                   (word_or
                     (word_or
                       (word_xor (word(bigdigit x 0)) (word(bigdigit y 0)))
                       (word_xor (word(bigdigit x 1)) (word(bigdigit y 1))))
                     (word_xor (word(bigdigit x 2)) (word(bigdigit y 2))))
                   (word_xor (word(bigdigit x 3))
                             (word(bigdigit y 3))):int64) = 0 <=>
              x = y)`;;

let WORD_OR_XOR_DIGITS_EQ_0 = assume_spec WORD_OR_XOR_DIGITS_EQ_0_STMT;;

let READ_MEMORY_BYTES64_BIGDIGIT_STMT =
  `!a:int64 m n j s:x86state.
        read (memory :> bytes(a,m)) s = n /\ 8 * j + 8 <= m
        ==> read (memory :> bytes64(word_add a (word(8 * j)))) s =
            word(bigdigit n j)`;;

let READ_MEMORY_BYTES64_BIGDIGIT = assume_spec READ_MEMORY_BYTES64_BIGDIGIT_STMT;;

(*** The four words of a 32-byte string n at a in state s ***)

let BIGDIGITS_32_TAC a n s =
  MAP_EVERY (fun j ->
    MP_TAC(SPECL [a; `32`; n; mk_small_numeral j; s]
      READ_MEMORY_BYTES64_BIGDIGIT) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC) (0--3);;

(*** The round constants in the image as wordlist_from_memory at the
 *** address that the simulation gives for them
 ***)

let MLKEM_NATIVE2_ROUND_CONSTANTS_STMT =
  `!s pc. bytes_loaded s (word pc) mlkem_native2_image_mc
          ==> wordlist_from_memory(word(pc + mlkem_native2_constants),24) s =
             round_constants`;;

let MLKEM_NATIVE2_ROUND_CONSTANTS = assume_spec MLKEM_NATIVE2_ROUND_CONSTANTS_STMT;;

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
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC exec (1--4) THEN
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native2_image_mc,exec,layout "mlkem_check_encoding",
    mlkem_check_encoding_mc,ceth)
   ([`read RDI s`; `n:num`; `pc + mlkem_check_encoding`] @ return_args) 5 THEN
  X86_STEPS_TAC exec (6--12) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `4096 = 2 EXP 12`] THEN
  W(fun (_,w) -> SPEC_TAC(find_term is_forall w,`b:bool`)) THEN
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  REPEAT(CHANGED_TAC
   (CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN REWRITE_TAC[]));;

(*** The RIP-relative addresses as the simulation gives them,
 *** word(val(word(pc + a)) + b), as word(pc + (a + b))
 ***)

let API_RIPREL_CONV =
  REWR_CONV WORD_VAL_ADD_64 THENC
  RAND_CONV(REWR_CONV(GSYM ADD_ASSOC) THENC RAND_CONV NUM_ADD_CONV);;

let API_RIPREL_TAC =
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV API_RIPREL_CONV));;

(*** The events of a callee given as e2 = f ... in the assumptions put in
 *** the facts about e2, for the discharge of memaccess_inbounds
 ***)

let SUBST_E2_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && is_var(lhand c) &&
       type_of(lhand c) = `:(uarch_event)list` &&
       String.length(name_of(lhand c)) >= 2 &&
       String.sub (name_of(lhand c)) 0 2 = "e2"
    then SUBST_ALL_TAC th else NO_TAC));;

let MLKEM_NATIVE2_CHECK_PK_SAFE_TAC exec =
  ASSUME_CALLEE_SAFETY_TAILED_TAC MLKEM_CHECK_ENCODING_SUBROUTINE_SAFE_FRAMED
    "H_CE" THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `pk:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 16 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC exec (1--4) THEN
  NATIVE2_SAFE_CALL_TAC mlkem_native2_image_mc exec
    [`pk:int64`; `pc:num`; `stackpointer:int64`; `returnaddress:int64`]
    "H_CE" (layout "mlkem_check_encoding",mlkem_check_encoding_mc)
    [`read RDI s`; `read RSI s`] 4 THEN
  X86_STEPS_TAC exec (6--12) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SUBST_E2_TAC THEN
  MEMACCESS_NUMERALS_TAC THEN NATIVE2_DISCHARGE_FRESH_TAC;;

let MLKEM_NATIVE2_CHECK_SK_CORRECT_TAC exec hoff =
  MAP_EVERY X_GEN_TAC
   [`sk:int64`; `ek:byte list`; `h:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 320 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** The hash of ek, with the round constants in the image ***)

  X86_STEPS_TAC exec (1--9) THEN API_RIPREL_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLKEM_NATIVE2_ROUND_CONSTANTS o
    check (can (term_match [] `bytes_loaded s (word pc) mc`) o concl)) THEN
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native2_image_mc,exec,0,
    mlkem_native2_image_mc,MLKEM_NATIVE_HASH_H_ASM_IMAGE_SUBROUTINE_CORRECT)
   ([`read RDI s`; `read RSI s`; `ek:byte list`; `read RCX s`; `pc:num`] @
    return_args) 10 THEN

  (*** The comparison with h, word by word ***)

  BIGDIGITS_32_TAC `word_add stackpointer (word 264):int64`
   `num_of_bytelist(sha3_256 ek)` `s10:x86state` THEN
  BIGDIGITS_32_TAC (mk_comb(`word_add (sk:int64)`,
                            mk_comb(`word:num->int64`,mk_small_numeral hoff)))
   `h:num` `s10:x86state` THEN
  X86_STEPS_TAC exec (11--29) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
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
                      `s:x86state`),`h:num`))) o concl)) THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; ARITH_RULE `256 = 8 * 32`;
                  READ_BYTES_BOUND]];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[EQ_SYM_EQ] THEN COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV;;

let MLKEM_NATIVE2_CHECK_SK_SAFE_TAC exec eklen =
  ASSUME_CALLEE_SAFETY_TAILED_TAC MLKEM_NATIVE_HASH_H_ASM_IMAGE_SUBROUTINE_SAFE "H_HASH" THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `sk:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 320 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC exec (1--9) THEN API_RIPREL_TAC THEN
  REMOVE_THEN "H_HASH" (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native2_image_mc,exec,0,mlkem_native2_image_mc,safety_th)
      ([`e:(uarch_event)list`; `read RDI s`; `read RSI s`;
        mk_small_numeral eklen; `read RCX s`; `pc:num`] @ return_args) 10
    THENL
     [EXISTS_E2_TAC (ref [`sk:int64`; `pc:num`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC "H_HASH" safety_th]) THEN
  X86_STEPS_TAC exec (11--29) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN SUBST_E2_TAC THEN
  MEMACCESS_NUMERALS_TAC THEN NATIVE2_DISCHARGE_FRESH_TAC;;
