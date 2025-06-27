(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

use_file_raise_failure := true;;
arm_print_log := true;;

needs "arm/proofs/base.ml";;
loadt "arm/proofs/aes_decrypt_spec.ml";;

print_literal_from_elf "arm/aes-xts/aes256_decrypt.o";;

let aes256_decrypt_mc = define_assert_from_elf "aes256_decrypt_mc" "arm/aes-xts/aes256_decrypt.o"
[
  0xb940f046;       (* arm_LDR W6 X2 (Immediate_Offset (word 0xf0)) *)
  0x4cdf7040;       (* arm_LDR Q0 X2 (Postimmediate_Offset (word 0x10)) *)
  0x4c407026;       (* arm_LDR Q6 X1 No_Offset *)
  0x510008c6;       (* arm_SUB W6 W6 (rvalue (word 0x2)) *)
  0x4cdf7041;       (* arm_LDR Q1 X2 (Postimmediate_Offset (word 0x10)) *)
  0x4e285806;       (* arm_AESD Q6 Q0 *)
  0x4e2878c6;       (* arm_AESIMC Q6 Q6 *)
  0x4cdf7840;       (* arm_LDR Q0 X2 (Postimmediate_Offset (word 0x10)) *)
  0x710008c6;       (* arm_SUBS W6 W6 (rvalue (word 0x2)) *)
  0x4e285826;       (* arm_AESD Q6 Q1 *)
  0x4e2878c6;       (* arm_AESIMC Q6 Q6 *)
  0x4cdf7841;       (* arm_LDR Q1 X2 (Postimmediate_Offset (word 0x10)) *)
  0x54ffff2c;       (* arm_BGT (word 0x1fffe4) *)
  0x4e285806;       (* arm_AESD Q6 Q0 *)
  0x4e2878c6;       (* arm_AESIMC Q6 Q6 *)
  0x4c407840;       (* arm_LDR Q0 X2 No_Offset *)
  0x4e285826;       (* arm_AESD Q6 Q1 *)
  0x6e201cc6;       (* arm_EOR_VEC Q6 Q6 Q0 0x80 *)
  0x4c007806        (* arm_STR Q6 X0 No_Offset *)
];;

let AES256_DECRYPT_EXEC = ARM_MK_EXEC_RULE aes256_decrypt_mc;;

(* TODO: Could this be better? read(memory :> bytes(key, 240) = all_k) *)
let AES256_DECRYPT_CORRECT = prove(
  `!plaintext ciphertext key ib k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 pc.
    nonoverlapping (word pc,LENGTH aes256_decrypt_mc) (plaintext,16)
    ==> ensures arm
      // precondition
      (\s. aligned_bytes_loaded s (word pc) aes256_decrypt_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [plaintext; ciphertext; key] s /\
           read(memory :> bytes128 ciphertext) s = ib /\
           read(memory :> bytes32 (word_add key (word 240))) s = word 14 /\
           read(memory :> bytes128 key) s = k0 /\
           read(memory :> bytes128 (word_add key (word 16))) s = k1 /\
           read(memory :> bytes128 (word_add key (word 32))) s = k2 /\
           read(memory :> bytes128 (word_add key (word 48))) s = k3 /\
           read(memory :> bytes128 (word_add key (word 64))) s = k4 /\
           read(memory :> bytes128 (word_add key (word 80))) s = k5 /\
           read(memory :> bytes128 (word_add key (word 96))) s = k6 /\
           read(memory :> bytes128 (word_add key (word 112))) s = k7 /\
           read(memory :> bytes128 (word_add key (word 128))) s = k8 /\
           read(memory :> bytes128 (word_add key (word 144))) s = k9 /\
           read(memory :> bytes128 (word_add key (word 160))) s = k10 /\
           read(memory :> bytes128 (word_add key (word 176))) s = k11 /\
           read(memory :> bytes128 (word_add key (word 192))) s = k12 /\
           read(memory :> bytes128 (word_add key (word 208))) s = k13 /\
           read(memory :> bytes128 (word_add key (word 224))) s = k14)
      // postcondition
      (\s. read PC s = word (pc + LENGTH aes256_decrypt_mc) /\
           read (memory :> bytes128 plaintext) s =
             aes256_decrypt ib [k0; k1; k2; k3; k4; k5; k6; k7; k8; k9; k10; k11; k12; k13; k14]
        )
      // MAYCHANGE
      (MAYCHANGE [PC;X6;X2] ,, MAYCHANGE [Q0; Q1; Q6],,
       MAYCHANGE [memory :> bytes128 plaintext],,
       MAYCHANGE SOME_FLAGS,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`plaintext:int64`; `ciphertext:int64`; `key:int64`;
    `ib:int128`; `k0:int128`; `k1:int128`; `k2:int128`;
    `k3:int128`; `k4:int128`; `k5:int128`; `k6:int128`;
    `k7:int128`; `k8:int128`; `k9:int128`; `k10:int128`;
    `k11:int128`; `k12:int128`; `k13:int128`; `k14:int128`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS;NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC [(REWRITE_CONV [aes256_decrypt_mc] THENC LENGTH_CONV) `LENGTH aes256_decrypt_mc`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_ACCSTEPS_TAC AES256_DECRYPT_EXEC [] (1--59) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  REWRITE_TAC [aes256_decrypt] THEN
  REWRITE_TAC EL_15_128_CLAUSES THEN
  REWRITE_TAC [aes256_decrypt_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC [aesd;aesimc] THEN
  GEN_REWRITE_TAC LAND_CONV [WORD_XOR_SYM] THEN
  REFL_TAC
);;
