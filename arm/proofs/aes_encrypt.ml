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
  0x4c407880;       (* arm_LDR Q0 X4 No_Offset *)
  0x4e284826;       (* arm_AESE Q6 Q1 *)
  0x6e201cc6;       (* arm_EOR_VEC Q6 Q6 Q0 128 *)
  0x4c007806        (* arm_STR Q6 X0 No_Offset *)
];;

let AES256_ENCRYPT_EXEC = ARM_MK_EXEC_RULE aes256_encrypt_mc;;

(* TODO: Could this be better? read(memory :> bytes(key, 240) = all_k) *)
let AES256_ENCRYPT_CORRECT = prove(
  `!out in key ib k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 pc.
    nonoverlapping (word pc,LENGTH aes256_encrypt_mc) (out,16)
    ==> ensures arm
      // precondition
      (\s. aligned_bytes_loaded s (word pc) aes256_encrypt_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [out; in; key] s /\
           read(memory :> bytes(in, 16)) s = ib /\
           read(memory :> bytes(word_add key (word 240), 4)) = word 13 /\
           read(memory :> bytes(key, 16)) = k0 /\
           read(memory :> bytes((word_add key (word 16)), 16)) = k1 /\
           read(memory :> bytes((word_add key (word 32)), 16)) = k2 /\
           read(memory :> bytes((word_add key (word 48)), 16)) = k3 /\
           read(memory :> bytes((word_add key (word 64)), 16)) = k4 /\
           read(memory :> bytes((word_add key (word 80)), 16)) = k5 /\
           read(memory :> bytes((word_add key (word 96)), 16)) = k6 /\
           read(memory :> bytes((word_add key (word 112)), 16)) = k7 /\
           read(memory :> bytes((word_add key (word 128)), 16)) = k8 /\
           read(memory :> bytes((word_add key (word 144)), 16)) = k9 /\
           read(memory :> bytes((word_add key (word 160)), 16)) = k10 /\
           read(memory :> bytes((word_add key (word 176)), 16)) = k11 /\
           read(memory :> bytes((word_add key (word 192)), 16)) = k12 /\
           read(memory :> bytes((word_add key (word 208)), 16)) = k13 /\
           read(memory :> bytes((word_add key (word 224)), 16)) = k14)
      // postcondition
      // TODO: Nevine will figure out the post condition for output
      // hint: use the aes256_encrypt from aes_encrypt_spec
      (\s. read PC s = word (pc + LENGTH aes256_encrypt_mc) /\
           )
      // MAYCHANGE
      ()`,
  CHEAT_TAC
)