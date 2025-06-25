needs "arm/proofs/base.ml";;
needs "arm/proofs/aes_encrypt_spec.ml";;

print_literal_from_elf "arm/aes-xts/aes256_encrypt.o";;

let aes256_encrypt_mc = define_assert_from_elf "aes256_encrypt_mc" "arm/aes-xts/aes256_encrypt.o"
[
  0xb940f046;       (* arm_LDR W6 X2 (Immediate_Offset (word 240)) *)
  0x4cdf7040;       (* arm_LDR Q0 X2 (Postimmediate_Offset (word 16)) *)
  0x4c407026;       (* arm_LDR Q6 X1 No_Offset *)
  0x510008c6;       (* arm_SUB W6 W6 (rvalue (word 2)) *)
  0x4cdf7041;       (* arm_LDR Q1 X2 (Postimmediate_Offset (word 16)) *)
  0x4e284806;       (* arm_AESE Q6 Q0 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4cdf7840;       (* arm_LDR Q0 X2 (Postimmediate_Offset (word 16)) *)
  0x710008c6;       (* arm_SUBS W6 W6 (rvalue (word 2)) *)
  0x4e284826;       (* arm_AESE Q6 Q1 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4cdf7841;       (* arm_LDR Q1 X2 (Postimmediate_Offset (word 16)) *)
  0x54ffff2c;       (* arm_BGT (word 2097124) *)
  0x4e284806;       (* arm_AESE Q6 Q0 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4c407840;       (* arm_LDR Q0 X2 No_Offset *)
  0x4e284826;       (* arm_AESE Q6 Q1 *)
  0x6e201cc6;       (* arm_EOR_VEC Q6 Q6 Q0 128 *)
  0x4c007806        (* arm_STR Q6 X0 No_Offset *)
];;

let AES256_ENCRYPT_EXEC = ARM_MK_EXEC_RULE aes256_encrypt_mc;;

(* TODO: Could this be better? read(memory :> bytes(key, 240) = all_k) *)

let AES256_ENCRYPT_CORRECT = prove(
  `!ciphertext plaintext key ib k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 pc.
    nonoverlapping (word pc,LENGTH aes256_encrypt_mc) (ciphertext,16)
    ==> ensures arm
      // precondition
      (\s. aligned_bytes_loaded s (word pc) aes256_encrypt_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [ciphertext; plaintext; key] s /\
           read(memory :> bytes128 plaintext) s = ib /\
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
           read(memory :> bytes128 (word_add key (word 224))) s = k14
      )
      // postcondition
      // TODO: Nevine will figure out the post condition for output
      // hint: use the aes256_encrypt from aes_encrypt_spec
      (\s. read PC s = word (pc + LENGTH aes256_encrypt_mc) /\
           read(memory :> bytes128 ciphertext) s =
              aes256_encrypt ib
                [k0; k1; k2; k3; k4; k5; k6; k7; k8; k9; k10; k11; k12; k13; k14]
      )
      (MAYCHANGE [PC;X2;X6],, MAYCHANGE [Q0;Q1;Q6],, MAYCHANGE [events],,
       MAYCHANGE SOME_FLAGS,, MAYCHANGE [memory :> bytes128 ciphertext])`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; C_ARGUMENTS; SOME_FLAGS] THEN
  REWRITE_TAC [(REWRITE_CONV [aes256_encrypt_mc] THENC LENGTH_CONV) `LENGTH aes256_encrypt_mc`] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES256_ENCRYPT_EXEC (1--5) THEN
  (* 1 loop iteration is 8 steps *)
  ARM_STEPS_TAC AES256_ENCRYPT_EXEC (6--13) THEN
  (* 5 more iterations = 8*5 = 40 steps *)
  ARM_STEPS_TAC AES256_ENCRYPT_EXEC (14--53) THEN
  (* 6 final steps *)
  ARM_STEPS_TAC AES256_ENCRYPT_EXEC (54--58) THEN
  ARM_STEPS_TAC AES256_ENCRYPT_EXEC (59--59) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC [aes256_encrypt] THEN
  REWRITE_TAC EL_15_128_CLAUSES THEN
  REWRITE_TAC [aes256_encrypt_round; aese; aesmc]
  CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
  BITBLAST_TAC
  (* Alternatively, use the XOR symmetry
  GEN_REWRITE_TAC LAND_CONV [WORD_XOR_SYM] THEN
    REFL_TAC *)
);;
