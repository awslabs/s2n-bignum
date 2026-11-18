(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* XOR of bytes into four Keccak states: the proof (see                      *)
(* keccakf1600x4_xor_bytes_spec.ml). The proof is that of the same code in   *)
(* the x86 gcc12_O2 image of mlkem-native, with the names changed.           *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/keccakf1600x4_xor_bytes_spec.ml";;
needs "x86/proofs/utils/mldsa_native_full.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. The four states, each a     *)
(* 1600-bit word as for mldsa_keccakf1600_xor_bytes, are consecutive in      *)
(* memory. The data for the states, which are only read, may overlap, e.g.   *)
(* all be the same. Each state is restated in the wbytes form for its call,  *)
(* and the result back as 200 bytes.                                         *)
(* ------------------------------------------------------------------------- *)

let XOR_BYTES_X4_CS_CALL_TAC sv dv n =
  KECCAK_STATE_WBYTES_TAC sv THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc
   MLDSA_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_EXEC "H_XOR_BYTES"
   [`read RDI s`; `read RSI s`; `off:num`; `len:num`; sv; dv; `pc:num`;
    `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   [`pc:num`; `a:int64`; `d0:int64`; `d1:int64`; `d2:int64`; `d3:int64`;
    `off:num`; `len:num`; `stackpointer:int64`; `returnaddress:int64`] n THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]);;

let MLDSA_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_XOR_BYTES" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun (n,c) -> ENSURES_PRESERVED_TAC n c)
   [("rbx_init",`RBX`); ("rbp_init",`RBP`); ("r12_init",`R12`);
    ("r13_init",`R13`); ("r14_init",`R14`); ("r15_init",`R15`)] THEN
  FULL_INIT_TAC THEN
  X86_STEPS_TAC MLDSA_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_EXEC
   (1--16) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  XOR_BYTES_X4_CS_CALL_TAC `S0:1600 word` `m0:num` 17 THEN
  X86_STEPS_TAC MLDSA_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_EXEC
   (18--22) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  XOR_BYTES_X4_CS_CALL_TAC `S1:1600 word` `m1:num` 23 THEN
  X86_STEPS_TAC MLDSA_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_EXEC
   (24--28) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  XOR_BYTES_X4_CS_CALL_TAC `S2:1600 word` `m2:num` 29 THEN
  X86_STEPS_TAC MLDSA_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_EXEC
   (30--41) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  XOR_BYTES_X4_CS_CALL_TAC `S3:1600 word` `m3:num` 42 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
