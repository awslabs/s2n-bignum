(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Expansion of the matrix from rho: the proof (see                          *)
(* polyvec_matrix_expand_eager_65_spec.ml).                                  *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/polyvec_matrix_expand_eager_65_spec.ml";;
needs "x86/proofs/utils/mldsa_native_sampling.ml";;
needs "x86/proofs/utils/mldsa_native_realign.ml";;
needs "x86/proofs/utils/mldsa_native_matrix.ml";;
needs "x86/proofs/utils/mldsa_native_scalar.ml";;

let MEXP65_EXEC = MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_EXEC;;

let MEXP65_ALLOWED =
  [`pc:num`; `mat:int64`; `rho:int64`; `r:num`; `stackpointer:int64`;
   `returnaddress:int64`; `bot:int64`];;

(* ------------------------------------------------------------------------- *)
(* The frame: 48 bytes are pushed before the AND, so that k = 5118 and the   *)
(* aligned frame and the stacks of the callees are the region (bot,5087),    *)
(* with the four buffers of 64 bytes at bot + 4831 + 64 * m, at RSP after    *)
(* the frame is reserved, aligned to 32 bytes, and the stacks of the callees *)
(* below them, with their return addresses. The code is simulated with the   *)
(* loops unrolled: the copies of rho, and for each group of four entries     *)
(* their indices and the call of mldsa_poly_uniform_4x, with the addresses   *)
(* of the entries restated for it (MEXP_ARGS_TAC); then the last two entries *)
(* with mldsa_poly_uniform, the indices of each loaded as a 16-bit constant  *)
(* from the read-only data and stored after rho in the first buffer.         *)
(* ------------------------------------------------------------------------- *)

let MEXP65_CALL_TAC g n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc MEXP65_EXEC "H_X4"
   ([`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `read R8 s`] @
    map (fun m -> let e = 4 * g + m in MEXP_SEED (e / 5) (e mod 5))
        (0--3) @
    [`pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`])
   MEXP65_ALLOWED n;;

let MEXP65_GROUP_TAC g =
  let s0 = 39 + 100 * g in
  let st = mk_var("s"^string_of_int (s0 + 96),`:x86state`) in
  X86_STEPS_TAC MEXP65_EXEC (s0--(s0 + 1)) THEN
  MAP_EVERY (fun m ->
    X86_STEPS_TAC MEXP65_EXEC ((s0 + 2 + 12 * m)--(s0 + 13 + 12 * m)) THEN
    PTR_DECIDE_RIP_TAC) (0--3) THEN
  X86_STEPS_TAC MEXP65_EXEC ((s0 + 50)--(s0 + 96)) THEN
  MAP_EVERY (fun m ->
    let e = 4 * g + m in
    MEXP_INPUT_TAC `bot:int64` (4831 + 64 * m) (e / 5) (e mod 5) st)
   (0--3) THEN
  MEXP_ARGS_TAC THEN MEXP65_CALL_TAC g (s0 + 97) THEN
  X86_STEPS_TAC MEXP65_EXEC ((s0 + 98)--(s0 + 99));;

(*** The two constants with the indices of the last two entries, and the ***)
(*** RIP-relative loads of them, as IMAGE_RIPREL_TAC (without alignment)  ***)

let MEXP65_CONSTANTS =
  map (fun d -> IMAGE_CONST_RULE_FOR mldsa_native_libmldsa_gcc12_O2_mc d 16)
   [layout "mldsa65_polyvec_matrix_expand_eager_const1";
    layout "mldsa65_polyvec_matrix_expand_eager_const2"];;

let MEXP65_RIPREL_TAC =
  let word_tm = `word:num->int64`
  and val_tm = `val:int64->num`
  and plus_tm = `(+):num->num->num` in
  fun th r ->
    FIRST_ASSUM(fun bth ->
      let cth = MATCH_MP th bth in
      let l = lhs(concl cth) in
      let wad = rand(rand(rand(rator l))) in
      let p,dt = dest_binop plus_tm (rand wad) in
      let d = dest_small_numeral dt in
      let rt = mk_small_numeral r and kt = mk_small_numeral(d - r) in
      let addr = mk_comb(word_tm,
        mk_binop plus_tm
         (mk_comb(val_tm,mk_comb(word_tm,mk_binop plus_tm p rt))) kt) in
      let eqth = CONV_RULE(RAND_CONV(RAND_CONV NUM_REDUCE_CONV))
        (REWRITE_CONV[RIPREL_ADDR_LEMMA; GSYM ADD_ASSOC] addr) in
      ASSUME_TAC(REWRITE_RULE[SYM eqth] cth));;

let MEXP65_SINGLE_TAC c j n =
  let r = layout "mldsa65_polyvec_matrix_expand_eager" +
          (if c = 0 then 0x129 else 0x144) in
  MEXP65_RIPREL_TAC (el c MEXP65_CONSTANTS) r THEN
  X86_STEPS_TAC MEXP65_EXEC (n--(n + 4)) THEN
  MEXP_INPUT_TAC `bot:int64` 4831 5 j
   (mk_var("s"^string_of_int(n + 4),`:x86state`)) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc MEXP65_EXEC "H_ONE"
   [`read RDI s`; `read RSI s`; MEXP_SEED 5 j;
    `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   MEXP65_ALLOWED (n + 5);;

(* ------------------------------------------------------------------------- *)
(* The setup: the callee theorems, the realigned stack frame, with the       *)
(* alignment of the stores of rho to the buffers, and the saved registers.   *)
(* ------------------------------------------------------------------------- *)

let MEXP65_SETUP_TAC =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_X4" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_ONE" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MEXP65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REALIGN_TAC 5118 THEN REALIGN_ALIGNED_TAC [4831] THEN
  SAMPLING_ALIGNED_FROM_TAC `bot:int64` 4831 16 [4895; 4959; 5023; 5087] THEN
  REALIGN_FRAME_TAC 5166 5118 THEN
  REALIGN_NONOV_TAC 5087
   [`mat:int64,30720`; `rho:int64,32`; `word pc:int64,51232`;
    `word_add stackpointer (word 5118):int64,48`;
    `word_add stackpointer (word 5166):int64,8`] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15`;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together. The two halves of  *)
(* rho are loaded into the YMM registers named at the start, so that the     *)
(* facts for their new low 128 bits are kept, and RSP gets the value of the  *)
(* AND after step 9.                                                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  MEXP65_SETUP_TAC THEN FULL_INIT_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MLD_BYTES128_HALVES o check
   (can (term_match [] `read (memory :> bytes(rho,32)) s = n`) o concl)) THEN
  STRIP_TAC THEN
  SAMPLING_GHOST_REGS_TAC [`YMM0`; `YMM1`] "s0" THEN

  (*** The prologue and the copies of rho ***)

  X86_STEPS_TAC MEXP65_EXEC (1--9) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC MEXP65_EXEC (10--15) THEN
  MAP_EVERY (fun m ->
    X86_STEPS_TAC MEXP65_EXEC ((16 + 5 * m)--(20 + 5 * m)) THEN
    PTR_DECIDE_RIP_TAC) (0--3) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SAMPLING_SUBWORD_JOIN_128]) THEN
  X86_STEPS_TAC MEXP65_EXEC (36--38) THEN
  MEXP_SETUP_TAC 6 5 `s38:x86state` THEN

  (*** The entries, and the epilogue ***)

  MAP_EVERY MEXP65_GROUP_TAC (0--6) THEN
  MEXP65_SINGLE_TAC 0 3 739 THEN MEXP65_SINGLE_TAC 1 4 745 THEN
  X86_STEPS_TAC MEXP65_EXEC (751--762) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MEXP_JOIN_TAC 30;
    REALIGN_UNBOT_TAC THEN SAMPLING_PATH_DISCHARGE_SPINE_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
   MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
   MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
