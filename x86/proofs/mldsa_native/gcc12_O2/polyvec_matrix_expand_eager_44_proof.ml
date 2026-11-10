(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Expansion of the matrix from rho: the proof (see                          *)
(* polyvec_matrix_expand_eager_44_spec.ml).                                  *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/polyvec_matrix_expand_eager_44_spec.ml";;
needs "x86/proofs/utils/mldsa_native_sampling.ml";;
needs "x86/proofs/utils/mldsa_native_realign.ml";;
needs "x86/proofs/utils/mldsa_native_matrix.ml";;

let MEXP44_EXEC = MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_O2_EXEC;;

let MEXP44_ALLOWED =
  [`pc:num`; `mat:int64`; `rho:int64`; `r:num`; `stackpointer:int64`;
   `returnaddress:int64`; `bot:int64`];;

(* ------------------------------------------------------------------------- *)
(* The frame: 40 bytes are pushed before the AND, so that k = 5118 and the   *)
(* aligned frame and the stacks of the callees are the region (bot,5087),    *)
(* with the four buffers of 64 bytes at bot + 4831 + 64 * m, at RSP after    *)
(* the frame is reserved, aligned to 32 bytes, and the stacks of the callees *)
(* below them, with their return addresses. The code is simulated with the   *)
(* loops unrolled: the copies of rho, and for each group of four entries     *)
(* their indices and the call of mldsa_poly_uniform_4x, with the addresses   *)
(* of the entries restated for it (MEXP_ARGS_TAC).                           *)
(* ------------------------------------------------------------------------- *)

let MEXP44_CALL_TAC g n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc MEXP44_EXEC "H_X4"
   ([`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `read R8 s`] @
    map (fun m -> let e = 4 * g + m in MEXP_SEED (e / 4) (e mod 4))
        (0--3) @
    [`pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`])
   MEXP44_ALLOWED n;;

let MEXP44_GROUP_TAC g =
  let s0 = 36 + 64 * g in
  let st = mk_var("s"^string_of_int (s0 + 60),`:x86state`) in
  X86_STEPS_TAC MEXP44_EXEC (s0--(s0 + 1)) THEN
  MAP_EVERY (fun m ->
    X86_STEPS_TAC MEXP44_EXEC ((s0 + 2 + 10 * m)--(s0 + 11 + 10 * m)) THEN
    PTR_DECIDE_RIP_TAC) (0--3) THEN
  X86_STEPS_TAC MEXP44_EXEC ((s0 + 42)--(s0 + 60)) THEN
  MAP_EVERY (fun m ->
    let e = 4 * g + m in
    MEXP_INPUT_TAC `bot:int64` (4831 + 64 * m) (e / 4) (e mod 4) st)
   (0--3) THEN
  MEXP_ARGS_TAC THEN MEXP44_CALL_TAC g (s0 + 61) THEN
  X86_STEPS_TAC MEXP44_EXEC ((s0 + 62)--(s0 + 63));;

(* ------------------------------------------------------------------------- *)
(* The setup: the callee theorems, the realigned stack frame, with the       *)
(* alignment of the stores of rho to the buffers, and the saved registers.   *)
(* ------------------------------------------------------------------------- *)

let MEXP44_SETUP_TAC =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_X4" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MEXP44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REALIGN_TAC 5118 THEN SAMPLING_ALIGNED_BOT_TAC 5118 4831 16 THEN
  SAMPLING_ALIGNED_FROM_TAC `bot:int64` 4831 16 [4895; 4959; 5023; 5087] THEN
  REALIGN_FRAME_TAC 5158 5118 THEN
  REALIGN_NONOV_TAC 5087
   [`mat:int64,16384`; `rho:int64,32`; `word pc:int64,51232`;
    `word_add stackpointer (word 5118):int64,40`;
    `word_add stackpointer (word 5158):int64,8`] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14`;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together. The two halves of  *)
(* rho are loaded into the YMM registers named at the start, so that the     *)
(* facts for their new low 128 bits are kept, and RSP gets the value of the  *)
(* AND after step 8.                                                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  MEXP44_SETUP_TAC THEN FULL_INIT_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MLD_BYTES128_HALVES o check
   (can (term_match [] `read (memory :> bytes(rho,32)) s = n`) o concl)) THEN
  STRIP_TAC THEN
  SAMPLING_GHOST_REGS_TAC [`YMM0`; `YMM1`] "s0" THEN

  (*** The prologue and the copies of rho ***)

  X86_STEPS_TAC MEXP44_EXEC (1--8) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC MEXP44_EXEC (9--14) THEN
  MAP_EVERY (fun m ->
    X86_STEPS_TAC MEXP44_EXEC ((15 + 5 * m)--(19 + 5 * m)) THEN
    PTR_DECIDE_RIP_TAC) (0--3) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SAMPLING_SUBWORD_JOIN_128]) THEN
  X86_STEPS_TAC MEXP44_EXEC (35--35) THEN
  MEXP_SETUP_TAC 4 4 `s35:x86state` THEN

  (*** The entries, and the epilogue ***)

  MAP_EVERY MEXP44_GROUP_TAC (0--3) THEN
  X86_STEPS_TAC MEXP44_EXEC (292--302) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MEXP_JOIN_TAC 16;
    REALIGN_UNBOT_TAC THEN SAMPLING_PATH_DISCHARGE_SPINE_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
   MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
   MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
