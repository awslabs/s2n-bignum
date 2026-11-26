(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Product of a row of the matrix with a vector, in the NTT domain, with the *)
(* entries sampled on demand: the proof (see                                 *)
(* polyvec_matrix_pointwise_montgomery_row_lazy_87_spec.ml).                 *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyvec_matrix_pointwise_montgomery_row_lazy_87_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyvec_matrix_pointwise_montgomery_row_lazy_87_inline.ml";;
needs "x86/proofs/utils/mldsa_native_polyvec.ml";;
needs "x86/proofs/utils/mldsa_native_lazy_matrix.ml";;
needs "x86/proofs/utils/mldsa_native_matrix.ml";;
needs "x86/proofs/utils/mldsa_native_sampling.ml";;
needs "x86/proofs/utils/mldsa_native_realign.ml";;

let RL87_EXEC =
  MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The frame of 1646 bytes below the return address: the six registers that  *)
(* the function saves (k = 1598, so that the AND of the stack pointer is of  *)
(* word_add stackpointer (word 1598) after                                   *)
(* REPEAT_GEN_AND_OFFSET_STACKPTR_TAC), and the aligned part (bot,1567), the *)
(* 96 bytes of which at the top are the buffer of 64 bytes (rho, and the     *)
(* bytes j and i of the seed after it) with RSP at bot + 1471 after the SUB, *)
(* and the stack of mldsa_poly_uniform below RSP. The code is straight line  *)
(* but for the loops that clang has inlined, for which it has the lemmas of  *)
(* polyvec_matrix_pointwise_montgomery_row_lazy_87_inline.ml: the products   *)
(* of the entries by the polynomials of y (the first into t, the others into *)
(* the polynomial of the structure) and their sums into t.                   *)
(* ------------------------------------------------------------------------- *)

let RL87_ALLOWED =
  [`pc:num`; `t:int64`; `mat:int64`; `v:int64`; `rho:num`; `i:num`;
   `mf:int64`; `mc:int64`; `stackpointer:int64`; `returnaddress:int64`;
   `bot:int64`];;

let RL87_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc RL87_EXEC
   name (ilist @ [`pc:num`; `read RSP s`;
                  `read (memory :> bytes64 (read RSP s)) s`])
   RL87_ALLOWED n;;

let RL87_REGION_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc RL87_EXEC
   name ilist RL87_ALLOWED n;;

(* the byte i of the seed, as the code stores the low byte of R12 *)

let RL_BYTE_R12 = prove
 (`!n. n < 256
       ==> word(val(word_zx(word_zx(word n:int64):int32):int64) MOD 256):byte =
           word n`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64;
              DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `n < 4294967296 /\ n < 18446744073709551616`
   STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `n < 256` THEN ARITH_TAC; ASM_SIMP_TAC[MOD_LT]]);;

(* the sum after the last column, in the form of the definition *)

let RL87_ACCL = prove
 (`!rho i (y:num->int32).
     mld_lazy_acc rho i y 6 =
     (mld_poly_add (mld_poly_add (mld_poly_add (mld_poly_add (mld_poly_add (mld_poly_add (mld_poly_pointwise_montgomery (mld_matrix_entry rho i 0) y)
           (mld_poly_pointwise_montgomery (mld_matrix_entry rho i 1)
             (\j. y (256 + j))))
           (mld_poly_pointwise_montgomery (mld_matrix_entry rho i 2)
             (\j. y (512 + j))))
           (mld_poly_pointwise_montgomery (mld_matrix_entry rho i 3)
             (\j. y (768 + j))))
           (mld_poly_pointwise_montgomery (mld_matrix_entry rho i 4)
             (\j. y (1024 + j))))
           (mld_poly_pointwise_montgomery (mld_matrix_entry rho i 5)
             (\j. y (1280 + j))))
           (mld_poly_pointwise_montgomery (mld_matrix_entry rho i 6)
             (\j. y (1536 + j))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[num_CONV `6`; num_CONV `5`; num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`; mld_lazy_acc;
              MLD_POLY_OF_0; mld_poly_of] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let RL87_P1 = `mld_poly_pointwise_montgomery (mld_matrix_entry rho i 1)
                 (\j. (y:num->int32)(256 + j))`;;
let RL87_P2 = `mld_poly_pointwise_montgomery (mld_matrix_entry rho i 2)
                 (\j. (y:num->int32)(512 + j))`;;
let RL87_P3 = `mld_poly_pointwise_montgomery (mld_matrix_entry rho i 3)
                 (\j. (y:num->int32)(768 + j))`;;
let RL87_P4 = `mld_poly_pointwise_montgomery (mld_matrix_entry rho i 4)
                 (\j. (y:num->int32)(1024 + j))`;;
let RL87_P5 = `mld_poly_pointwise_montgomery (mld_matrix_entry rho i 5)
                 (\j. (y:num->int32)(1280 + j))`;;
let RL87_P6 = `mld_poly_pointwise_montgomery (mld_matrix_entry rho i 6)
                 (\j. (y:num->int32)(1536 + j))`;;
let RL87_A0 = `mld_poly_pointwise_montgomery (mld_matrix_entry rho i 0)
                 (y:num->int32)`;;
let RL87_A1 = mk_comb(mk_comb(`mld_poly_add`,RL87_A0),RL87_P1);;
let RL87_A2 = mk_comb(mk_comb(`mld_poly_add`,RL87_A1),RL87_P2);;
let RL87_A3 = mk_comb(mk_comb(`mld_poly_add`,RL87_A2),RL87_P3);;
let RL87_A4 = mk_comb(mk_comb(`mld_poly_add`,RL87_A3),RL87_P4);;
let RL87_A5 = mk_comb(mk_comb(`mld_poly_add`,RL87_A4),RL87_P5);;
let RL87_A6 = mk_comb(mk_comb(`mld_poly_add`,RL87_A5),RL87_P6);;

(* ------------------------------------------------------------------------- *)
(* The prologue: rho is loaded as two 128-bit words and stored to the buffer *)
(* with the bytes 0 and i after it; entry (i,0) is sampled into t and        *)
(* multiplied by polynomial 0 of y.                                          *)
(* ------------------------------------------------------------------------- *)

let RL87_SEED_TAC j s =
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP RL_BYTE_R12 (ASSUME `i < 256`)]) THEN
  MP_TAC(SPECL [`word_add bot (word 1471):int64`; `rho:num`; `i:num`;
                mk_small_numeral j; mk_var(s,`:x86state`)] LAZY_SEED) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    DISCH_TAC] THEN
  MLD_LAZY_TERM_TAC
   (mk_comb(`mld_rej_uniform_terminates`,
      mk_comb(mk_comb(`mld_shake128_stream`,`34`),
              list_mk_comb(`mld_matrix_seed`,
                [`rho:num`; `i:num`; mk_small_numeral j]))));;

let RL87_PROLOGUE_TAC =
  FULL_INIT_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MLD_BYTES128_HALVES o check
   (can (term_match []
     `read (memory :> bytes(word_add mat (word 1024),32)) s = n`) o concl)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `rho < 2 EXP 256` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check
     (can (term_match []
       `read (memory :> bytes(word_add mat (word 1024),32)) s = n`) o
      concl)) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
    MP_TAC(ISPECL [`word_add mat (word 1024):int64`; `32`;
                   `read memory (s0:x86state)`] READ_BYTES_BOUND) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SAMPLING_GHOST_REGS_TAC [`YMM0`; `YMM1`] "s0" THEN
  X86_STEPS_TAC RL87_EXEC (1--8) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC RL87_EXEC (9--22) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SAMPLING_SUBWORD_JOIN_128;
                              MATCH_MP RL_BYTE_R12 (ASSUME `i < 256`)]) THEN
  MP_TAC(SPECL [`word_add bot (word 1471):int64`; `rho:num`; `s22:x86state`]
               LAZY_RHO_OF_HALVES) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  RL87_SEED_TAC 0 "s22" THEN
  RL87_CALL_TAC "H_UNI" [`read RDI s`; `read RSI s`; `mld_matrix_seed rho i 0`]
   23 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_matrix_entry]) THEN
  X86_STEPS_TAC RL87_EXEC (24--25) THEN
  VEC_SLICE_TAC
   `!j. j < 256
        ==> read(memory :> bytes32(word_add v (word(4 * j)))) s25 =
            (y:num->int32) j` THEN
  RL87_REGION_TAC "H_PWM1"
   [`read RBX s`; `read R15 s`; `pc:num`; `mld_matrix_entry rho i 0`;
    `y:num->int32`] 26;;

(* ------------------------------------------------------------------------- *)
(* Column c = 1, 2, 3: the byte c after rho, the entry sampled into the      *)
(* polynomial of the structure and multiplied by polynomial c of y, and the  *)
(* sum into t, by the vector loop, which the code takes when the two         *)
(* polynomials do not overlap. s is the number of the step before the first  *)
(* of the column, and the lemmas of the column are those of its loops.       *)
(* ------------------------------------------------------------------------- *)

let RL87_COLUMN_TAC c s pwm add acc p =
  X86_STEPS_TAC RL87_EXEC ((s + 1)--(s + 5)) THEN
  RL87_SEED_TAC c ("s" ^ string_of_int (s + 5)) THEN
  RL87_CALL_TAC "H_UNI"
   [`read RDI s`; `read RSI s`;
    list_mk_comb(`mld_matrix_seed`,[`rho:num`; `i:num`; mk_small_numeral c])]
   (s + 6) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_matrix_entry]) THEN
  X86_STEPS_TAC RL87_EXEC ((s + 7)--(s + 8)) THEN
  VEC_SLICE_TAC
   (parse_term(Printf.sprintf
     "!j. j < 256
          ==> read(memory :> bytes32(word_add v (word(%d + 4 * j)))) s%d =
              (y:num->int32)(%d + j)" (1024 * c) (s + 8) (256 * c))) THEN
  RL87_REGION_TAC pwm
   [`read R14 s`; `read R15 s`; `pc:num`;
    list_mk_comb(`mld_matrix_entry`,[`rho:num`; `i:num`; mk_small_numeral c]);
    mk_abs(`j:num`,mk_comb(`y:num->int32`,
      mk_binop `(+):num->num->num` (mk_small_numeral(256 * c)) `j:num`))]
   (s + 9) THEN
  X86_STEPS_TAC RL87_EXEC ((s + 10)--(s + 17)) THEN
  RL_ALIAS_TAC THEN
  X86_STEPS_TAC RL87_EXEC ((s + 18)--(s + 19)) THEN
  RL87_REGION_TAC add
   [`read RBX s`; `read R14 s`; `pc:num`; acc; p] (s + 20);;

(* ------------------------------------------------------------------------- *)
(* The reduction of t, the zeroing of the buffer, and the return.            *)
(* ------------------------------------------------------------------------- *)

let RL87_CONST_RULE =
  IMAGE_CONST_RULE_FOR mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc;;

let RL87_LOAD_CONST_TAC k r =
  IMAGE_RIPREL_TAC (RL87_CONST_RULE (0x25000 + 16 * k) 128) (0x1f350 + r);;

let RL87_XMM_TAC k xmm s v =
  SUBGOAL_THEN (parse_term(Printf.sprintf "read XMM%d (%s:x86state) = word %s" k s v))
   ASSUME_TAC THENL
   [REWRITE_TAC[xmm; READ_ZEROTOP_128] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST;
    ALL_TAC];;

let RL87_BODY_TAC =
  RL87_PROLOGUE_TAC THEN
  RL87_COLUMN_TAC 1 26 "H_PWM2" "H_ADD2" RL87_A0 RL87_P1 THEN
  RL87_COLUMN_TAC 2 46 "H_PWM3" "H_ADD3" RL87_A1 RL87_P2 THEN
  RL87_COLUMN_TAC 3 66 "H_PWM4" "H_ADD4" RL87_A2 RL87_P3 THEN
  RL87_COLUMN_TAC 4 86 "H_PWM5" "H_ADD5" RL87_A3 RL87_P4 THEN
  RL87_COLUMN_TAC 5 106 "H_PWM6" "H_ADD6" RL87_A4 RL87_P5 THEN
  RL87_COLUMN_TAC 6 126 "H_PWM7" "H_ADD7" RL87_A5 RL87_P6 THEN
  X86_STEPS_TAC RL87_EXEC (147--147) THEN
  SAMPLING_GHOST_REGS_TAC [`YMM0`; `YMM1`] "s147" THEN
  RL87_LOAD_CONST_TAC 0 0x8af THEN RL87_LOAD_CONST_TAC 1 0x8b7 THEN
  X86_STEPS_TAC RL87_EXEC (148--150) THEN
  RL87_XMM_TAC 0 XMM0 "s150" "0x00400000004000000040000000400000" THEN
  RL87_XMM_TAC 1 XMM1 "s150" "0xff801fffff801fffff801fffff801fff" THEN
  RL87_REGION_TAC "H_RED" [`read RBX s`; `pc:num`; RL87_A6] 151 THEN
  REALIGN_ALIGNED_TAC [1487; 1503; 1519] THEN
  X86_STEPS_TAC RL87_EXEC (152--170) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[mld_polyvec_matrix_row_lazy] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
  REWRITE_TAC[RL87_ACCL] THEN ASM_REWRITE_TAC[] THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together.                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP
       MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
       th) "H_UNI" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC RL87_PWM1 "H_PWM1" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC RL87_PWM2 "H_PWM2" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC RL87_PWM3 "H_PWM3" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC RL87_PWM4 "H_PWM4" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC RL87_PWM5 "H_PWM5" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC RL87_PWM6 "H_PWM6" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC RL87_PWM7 "H_PWM7" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC RL87_ADD2 "H_ADD2" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC RL87_ADD3 "H_ADD3" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC RL87_ADD4 "H_ADD4" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC RL87_ADD5 "H_ADD5" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC RL87_ADD6 "H_ADD6" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC RL87_ADD7 "H_ADD7" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC RL87_RED "H_RED") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(t:int64) (mat:int64) (v:int64) (rho:num) (i:num) (mf:int64)
     (mc:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
     f_ev_all t mat v rho i mf mc pc stackpointer returnaddress
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst RL87_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REALIGN_TAC 1598 THEN REALIGN_FRAME_TAC 1646 1598 THEN
  REALIGN_NONOV_TAC 1567
   [`t:int64,1024`; `mat:int64,1024`; `word_add mat (word 1024):int64,32`;
    `v:int64,7168`; `word pc:int64,libmldsa_size`;
    `word(pc + got_memset):int64,8`; `word(pc + got_memcpy):int64,8`;
    `ea:int64,el:num`;
    `word_add stackpointer (word 1598):int64,48`;
    `word_add stackpointer (word 1646):int64,8`] THEN
  REALIGN_ALIGNED_TAC [1471] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15` THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[mld_matrix_terminates] o check
   (can (term_match [] `mld_matrix_terminates 8 7 rho`) o concl)) THEN
  SUBGOAL_THEN `i < 256` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  RL87_BODY_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    CORRECT_OF_FULL_TAC
     (MP (SPEC_ALL
       MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    SAFE_OF_FULL_TAC
     (MP (SPEC_ALL
       MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;
