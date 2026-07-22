(* ========================================================================= *)
(* AESV8_GCM_8X_DEC_256_WB: the whole-blocks-only decrypt variant.            *)
(*                                                                            *)
(* Binary: arm/aes-gcm/aesv8_gcm_8x_dec_256_wb.S (see its header) — the       *)
(* production aws-lc unroll8 decrypt with (1) an entry guard aborting (ret 0, *)
(* no memory touched) unless bit_len is a nonzero multiple of 128, and (2)    *)
(* the partial-block masking machinery deleted from the tail (dead under the  *)
(* contract; it carried a 16-byte overread + read-modify-write of the output).*)
(* 4560 bytes; C_ARGUMENTS proof entry at pc+0x20 (post-saves).               *)
(*                                                                            *)
(* Structure (shared symbolic front + exhaustive concrete tails):             *)
(*  - WB_FRONT_BUF: ONE front lemma (entry pc+0x20 -> pc+3796) symbolic in    *)
(*    nblk (bit_len = 128*nblk, 1<=nblk<=8), buffer-form input                *)
(*    (read bytes(in_p,16*nblk) = num_of_bytelist ibytes).  The front's only  *)
(*    conditional branch (b.ge pc+0x42c) is nblk-independent: the byte count  *)
(*    ANDed with ~127 collapses to 0 (AND_MASK_16NBLK), so the loop-skip      *)
(*    compare is in_p vs in_p.  Its postcondition is the harvested 70-conjunct*)
(*    s265 machine state (built programmatically -- the 8 in-flight 13-round  *)
(*    aese/aesmc keystream towers cannot be hand-written), INCLUDING          *)
(*    aligned_bytes_loaded (required for the tails to keep stepping).         *)
(*  - AESV8_GCM_8X_DEC_256_WB_BUF_{1..8}BLOCK: the 8 fixed-size band theorems *)
(*    (bit_len = 128*N), each = ENSURES_FRAME_SUBSUMED + ENSURES_TRANS at     *)
(*    pc+3796 with the front leg discharged by WB_FRONT_BUF and the back leg  *)
(*    the band tail (cascade + GHASH + bridge + stores) from the shared state.*)
(*    (ENSURES_SEQUENCE_TAC itself throws MAYCHANGE_IDEMPOT on the 4-memory-  *)
(*    region frame; the SUBSUMED+TRANS route is the le1block lesson.)         *)
(*    Statements are buffer-form: outputs and the GHASH list are over         *)
(*    bytes_to_int128 (SUB_LIST (16i,16) ibytes).                             *)
(*  - A guard-abort theorem (unchanged).                                      *)
(*                                                                            *)
(* Reuses the mask-agnostic machinery from the masked chain via core.ml       *)
(* (GHASH/Karatsuba bridge layer, SIMD-fold steppers).  JRH-style statement   *)
(* simplifications: AES256_XOR_ENCRYPT_RECONSTRUCT (machine aese/aesmc tower  *)
(* = aes256_encrypt, proved once) and the htable_mem_dec named memory         *)
(* predicate over the abstract key h.  No CHEAT_TAC, no new axioms.           *)
(* ========================================================================= *)

needs "arm/proofs/aesv8_gcm_8x_dec_256_core.ml";;
needs "arm/proofs/utils/aes_gcm_dec_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* Machine code (print_literal_from_elf "arm/aes-gcm/aesv8_gcm_8x_dec_256_wb.o") *)
(* ------------------------------------------------------------------------- *)

let aesv8_gcm_8x_dec_256_wb_mc = define_assert_from_elf "aesv8_gcm_8x_dec_256_wb_mc"
  "arm/aes-gcm/aesv8_gcm_8x_dec_256_wb.o"
[
  0xd503201f;       (* arm_NOP *)
  0xb4008e21;       (* arm_CBZ X1 (word 4548) *)
  0xf240183f;       (* arm_TST X1 (rvalue (word 127)) *)
  0x54008de1;       (* arm_BNE (word 4540) *)
  0x6dbb27e8;       (* arm_STP D8 D9 SP (Preimmediate_Offset (iword (-- &80))) *)
  0x6d012fea;       (* arm_STP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d0237ec;       (* arm_STP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d033fee;       (* arm_STP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0xd343fc29;       (* arm_LSR X9 X1 3 *)
  0xaa0403f0;       (* arm_MOV X16 X4 *)
  0xaa0503eb;       (* arm_MOV X11 X5 *)
  0xd2f84005;       (* arm_MOVZ X5 (word 49664) 48 *)
  0xa9047fe5;       (* arm_STP X5 XZR SP (Immediate_Offset (iword (&64))) *)
  0x910103ea;       (* arm_ADD X10 SP (rvalue (word 64)) *)
  0x4c407200;       (* arm_LDR Q0 X16 No_Offset *)
  0xd2c0002f;       (* arm_MOVZ X15 (word 1) 32 *)
  0x4f00e41f;       (* arm_MOVI Q31 (word 0) *)
  0x4e181dff;       (* arm_INS_GEN Q31 X15 64 64 *)
  0xaa0903e5;       (* arm_MOV X5 X9 *)
  0xd10004a5;       (* arm_SUB X5 X5 (rvalue (word 1)) *)
  0x6e20081e;       (* arm_REV32_VEC Q30 Q0 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x6e200bc1;       (* arm_REV32_VEC Q1 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x6e200bc2;       (* arm_REV32_VEC Q2 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xad406d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&0))) *)
  0x6e200bc3;       (* arm_REV32_VEC Q3 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x6e200bc4;       (* arm_REV32_VEC Q4 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e200bc5;       (* arm_REV32_VEC Q5 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x6e200bc6;       (* arm_REV32_VEC Q6 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x6e200bc7;       (* arm_REV32_VEC Q7 Q30 8 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0xad41697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&32))) *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xad42717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&64))) *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0xad436d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&96))) *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0xad44697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&128))) *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x9279e0a5;       (* arm_AND X5 X5 (rvalue (word 18446744073709551488)) *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4c407073;       (* arm_LDR Q19 X3 No_Offset *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e200a73;       (* arm_REV64_VEC Q19 Q19 8 *)
  0xad45717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&160))) *)
  0x8b410c04;       (* arm_ADD X4 X0 (Shiftedreg X1 LSR 3) *)
  0x8b0000a5;       (* arm_ADD X5 X5 X0 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xad466d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&192))) *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x3dc0397c;       (* arm_LDR Q28 X11 (Immediate_Offset (word 224)) *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0xeb05001f;       (* arm_CMP X0 X5 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x540054aa;       (* arm_BGE (word 2708) *)
  0xacc12408;       (* arm_LDP Q8 Q9 X0 (Postimmediate_Offset (iword (&32))) *)
  0xacc12c0a;       (* arm_LDP Q10 Q11 X0 (Postimmediate_Offset (iword (&32))) *)
  0xacc1340c;       (* arm_LDP Q12 Q13 X0 (Postimmediate_Offset (iword (&32))) *)
  0xacc13c0e;       (* arm_LDP Q14 Q15 X0 (Postimmediate_Offset (iword (&32))) *)
  0xeb05001f;       (* arm_CMP X0 X5 *)
  0xce017121;       (* arm_EOR3 Q1 Q9 Q1 Q28 *)
  0xce007100;       (* arm_EOR3 Q0 Q8 Q0 Q28 *)
  0xac810440;       (* arm_STP Q0 Q1 X2 (Postimmediate_Offset (iword (&32))) *)
  0x6e200bc0;       (* arm_REV32_VEC Q0 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xce037163;       (* arm_EOR3 Q3 Q11 Q3 Q28 *)
  0xce0571a5;       (* arm_EOR3 Q5 Q13 Q5 Q28 *)
  0xce047184;       (* arm_EOR3 Q4 Q12 Q4 Q28 *)
  0x6e200bc1;       (* arm_REV32_VEC Q1 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xce027142;       (* arm_EOR3 Q2 Q10 Q2 Q28 *)
  0xac810c42;       (* arm_STP Q2 Q3 X2 (Postimmediate_Offset (iword (&32))) *)
  0x6e200bc2;       (* arm_REV32_VEC Q2 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xce0671c6;       (* arm_EOR3 Q6 Q14 Q6 Q28 *)
  0x6e200bc3;       (* arm_REV32_VEC Q3 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xac811444;       (* arm_STP Q4 Q5 X2 (Postimmediate_Offset (iword (&32))) *)
  0xce0771e7;       (* arm_EOR3 Q7 Q15 Q7 Q28 *)
  0xac811c46;       (* arm_STP Q6 Q7 X2 (Postimmediate_Offset (iword (&32))) *)
  0x6e200bc4;       (* arm_REV32_VEC Q4 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x54002aaa;       (* arm_BGE (word 1364) *)
  0x6e200bc5;       (* arm_REV32_VEC Q5 Q30 8 *)
  0xad406d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&0))) *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e200929;       (* arm_REV64_VEC Q9 Q9 8 *)
  0x3dc024d7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 144)) *)
  0x3dc02cd9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 176)) *)
  0x6e200bc6;       (* arm_REV32_VEC Q6 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e200908;       (* arm_REV64_VEC Q8 Q8 8 *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e20098c;       (* arm_REV64_VEC Q12 Q12 8 *)
  0x4e20096b;       (* arm_REV64_VEC Q11 Q11 8 *)
  0x6e200bc7;       (* arm_REV32_VEC Q7 Q30 8 *)
  0x4e2009ef;       (* arm_REV64_VEC Q15 Q15 8 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0xad41697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&32))) *)
  0x6e331d08;       (* arm_EOR_VEC Q8 Q8 Q19 128 *)
  0x3dc018d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 96)) *)
  0x3dc020d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 128)) *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e20094a;       (* arm_REV64_VEC Q10 Q10 8 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4ec82932;       (* arm_TRN1 Q18 Q9 Q8 64 128 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x0ef9e113;       (* arm_PMULL_VEC Q19 Q8 Q25 64 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0xad42717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&64))) *)
  0x4ef6e15d;       (* arm_PMULL2_VEC Q29 Q10 Q22 64 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4ef7e130;       (* arm_PMULL2_VEC Q16 Q9 Q23 64 *)
  0x0ef7e137;       (* arm_PMULL_VEC Q23 Q9 Q23 64 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4ef9e111;       (* arm_PMULL2_VEC Q17 Q8 Q25 64 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4ec86928;       (* arm_TRN2 Q8 Q9 Q8 64 128 *)
  0x4ef4e169;       (* arm_PMULL2_VEC Q9 Q11 Q20 64 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x6e301e31;       (* arm_EOR_VEC Q17 Q17 Q16 128 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x3dc01cd5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 112)) *)
  0x3dc028d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 160)) *)
  0x6e321d08;       (* arm_EOR_VEC Q8 Q8 Q18 128 *)
  0x0ef6e156;       (* arm_PMULL_VEC Q22 Q10 Q22 64 *)
  0xad436d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&96))) *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e371e73;       (* arm_EOR_VEC Q19 Q19 Q23 128 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0xce1d2631;       (* arm_EOR3 Q17 Q17 Q29 Q9 *)
  0x4eca297d;       (* arm_TRN1 Q29 Q11 Q10 64 128 *)
  0x4e2009ad;       (* arm_REV64_VEC Q13 Q13 8 *)
  0x4ef8e112;       (* arm_PMULL2_VEC Q18 Q8 Q24 64 *)
  0x0ef8e118;       (* arm_PMULL_VEC Q24 Q8 Q24 64 *)
  0x4eca696a;       (* arm_TRN2 Q10 Q11 Q10 64 128 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4ecc29b0;       (* arm_TRN1 Q16 Q13 Q12 64 128 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x6e3d1d4a;       (* arm_EOR_VEC Q10 Q10 Q29 128 *)
  0x0ef4e174;       (* arm_PMULL_VEC Q20 Q11 Q20 64 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4ef5e15d;       (* arm_PMULL2_VEC Q29 Q10 Q21 64 *)
  0x0ef5e155;       (* arm_PMULL_VEC Q21 Q10 Q21 64 *)
  0xce165273;       (* arm_EOR3 Q19 Q19 Q22 Q20 *)
  0x3dc00cd7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 48)) *)
  0x3dc014d9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 80)) *)
  0x4e2009ce;       (* arm_REV64_VEC Q14 Q14 8 *)
  0x6e381e52;       (* arm_EOR_VEC Q18 Q18 Q24 128 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0xad44697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&128))) *)
  0x3dc000d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 0)) *)
  0x3dc008d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 32)) *)
  0xce157652;       (* arm_EOR3 Q18 Q18 Q21 Q29 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4ef9e188;       (* arm_PMULL2_VEC Q8 Q12 Q25 64 *)
  0x0ef9e199;       (* arm_PMULL_VEC Q25 Q12 Q25 64 *)
  0x4ecc69ac;       (* arm_TRN2 Q12 Q13 Q12 64 128 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4ef7e1aa;       (* arm_PMULL2_VEC Q10 Q13 Q23 64 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x0ef7e1b7;       (* arm_PMULL_VEC Q23 Q13 Q23 64 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4ef6e1cb;       (* arm_PMULL2_VEC Q11 Q14 Q22 64 *)
  0x4ece29ed;       (* arm_TRN1 Q13 Q15 Q14 64 128 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0xad45717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&160))) *)
  0x0ef6e1d6;       (* arm_PMULL_VEC Q22 Q14 Q22 64 *)
  0x4ece69ee;       (* arm_TRN2 Q14 Q15 Q14 64 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xce082a31;       (* arm_EOR3 Q17 Q17 Q8 Q10 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x6e2d1dce;       (* arm_EOR_VEC Q14 Q14 Q13 128 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0xacc12408;       (* arm_LDP Q8 Q9 X0 (Postimmediate_Offset (iword (&32))) *)
  0x6e301d8c;       (* arm_EOR_VEC Q12 Q12 Q16 128 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4ef5e1cd;       (* arm_PMULL2_VEC Q13 Q14 Q21 64 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4ef8e190;       (* arm_PMULL2_VEC Q16 Q12 Q24 64 *)
  0x0ef8e198;       (* arm_PMULL_VEC Q24 Q12 Q24 64 *)
  0x4ef4e1ec;       (* arm_PMULL2_VEC Q12 Q15 Q20 64 *)
  0x0ef4e1f4;       (* arm_PMULL_VEC Q20 Q15 Q20 64 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x0ef5e1d5;       (* arm_PMULL_VEC Q21 Q14 Q21 64 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xce195e73;       (* arm_EOR3 Q19 Q19 Q25 Q23 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xce184252;       (* arm_EOR3 Q18 Q18 Q24 Q16 *)
  0xce0b3231;       (* arm_EOR3 Q17 Q17 Q11 Q12 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xce165273;       (* arm_EOR3 Q19 Q19 Q22 Q20 *)
  0x6e200bd4;       (* arm_REV32_VEC Q20 Q30 8 *)
  0xfd400150;       (* arm_LDR D16 X10 (Immediate_Offset (word 0)) *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0xad466d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&192))) *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0xce153652;       (* arm_EOR3 Q18 Q18 Q21 Q13 *)
  0x6e200bd6;       (* arm_REV32_VEC Q22 Q30 8 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0xacc12c0a;       (* arm_LDP Q10 Q11 X0 (Postimmediate_Offset (iword (&32))) *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x6e114235;       (* arm_EXT Q21 Q17 Q17 64 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x6e200bd7;       (* arm_REV32_VEC Q23 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x0ef0e23d;       (* arm_PMULL_VEC Q29 Q17 Q16 64 *)
  0xce114e52;       (* arm_EOR3 Q18 Q18 Q17 Q19 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x3dc0397c;       (* arm_LDR Q28 X11 (Immediate_Offset (word 224)) *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xce1d5652;       (* arm_EOR3 Q18 Q18 Q29 Q21 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xacc1340c;       (* arm_LDP Q12 Q13 X0 (Postimmediate_Offset (iword (&32))) *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0xacc13c0e;       (* arm_LDP Q14 Q15 X0 (Postimmediate_Offset (iword (&32))) *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x6e200bd9;       (* arm_REV32_VEC Q25 Q30 8 *)
  0xce027142;       (* arm_EOR3 Q2 Q10 Q2 Q28 *)
  0xce017121;       (* arm_EOR3 Q1 Q9 Q1 Q28 *)
  0x6e124255;       (* arm_EXT Q21 Q18 Q18 64 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x0ef0e251;       (* arm_PMULL_VEC Q17 Q18 Q16 64 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0xce0571a5;       (* arm_EOR3 Q5 Q13 Q5 Q28 *)
  0xce007100;       (* arm_EOR3 Q0 Q8 Q0 Q28 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0xac810440;       (* arm_STP Q0 Q1 X2 (Postimmediate_Offset (iword (&32))) *)
  0x4eb41e80;       (* arm_MOV_VEC Q0 Q20 128 *)
  0xce047184;       (* arm_EOR3 Q4 Q12 Q4 Q28 *)
  0xce154673;       (* arm_EOR3 Q19 Q19 Q21 Q17 *)
  0xce037163;       (* arm_EOR3 Q3 Q11 Q3 Q28 *)
  0xac810c42;       (* arm_STP Q2 Q3 X2 (Postimmediate_Offset (iword (&32))) *)
  0x4eb91f23;       (* arm_MOV_VEC Q3 Q25 128 *)
  0x4eb71ee2;       (* arm_MOV_VEC Q2 Q23 128 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4eb61ec1;       (* arm_MOV_VEC Q1 Q22 128 *)
  0xac811444;       (* arm_STP Q4 Q5 X2 (Postimmediate_Offset (iword (&32))) *)
  0xce0771e7;       (* arm_EOR3 Q7 Q15 Q7 Q28 *)
  0xce0671c6;       (* arm_EOR3 Q6 Q14 Q6 Q28 *)
  0x6e200bc4;       (* arm_REV32_VEC Q4 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xeb05001f;       (* arm_CMP X0 X5 *)
  0xac811c46;       (* arm_STP Q6 Q7 X2 (Postimmediate_Offset (iword (&32))) *)
  0x54ffd5ab;       (* arm_BLT (word 2095796) *)
  0xad406d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&0))) *)
  0x6e200bc5;       (* arm_REV32_VEC Q5 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e20098c;       (* arm_REV64_VEC Q12 Q12 8 *)
  0x3dc01cd5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 112)) *)
  0x3dc028d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 160)) *)
  0x6e200bc6;       (* arm_REV32_VEC Q6 Q30 8 *)
  0x4e200908;       (* arm_REV64_VEC Q8 Q8 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x3dc024d7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 144)) *)
  0x3dc02cd9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 176)) *)
  0x4e200929;       (* arm_REV64_VEC Q9 Q9 8 *)
  0x6e200bc7;       (* arm_REV32_VEC Q7 Q30 8 *)
  0x4e20094a;       (* arm_REV64_VEC Q10 Q10 8 *)
  0x3dc018d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 96)) *)
  0x3dc020d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 128)) *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0xad41697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&32))) *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e331d08;       (* arm_EOR_VEC Q8 Q8 Q19 128 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4ef7e130;       (* arm_PMULL2_VEC Q16 Q9 Q23 64 *)
  0x4ec82932;       (* arm_TRN1 Q18 Q9 Q8 64 128 *)
  0x0ef9e113;       (* arm_PMULL_VEC Q19 Q8 Q25 64 *)
  0x4e20096b;       (* arm_REV64_VEC Q11 Q11 8 *)
  0x0ef7e137;       (* arm_PMULL_VEC Q23 Q9 Q23 64 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4ef9e111;       (* arm_PMULL2_VEC Q17 Q8 Q25 64 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e2009ce;       (* arm_REV64_VEC Q14 Q14 8 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4ef6e15d;       (* arm_PMULL2_VEC Q29 Q10 Q22 64 *)
  0x4ec86928;       (* arm_TRN2 Q8 Q9 Q8 64 128 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xad42717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&64))) *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4ef4e169;       (* arm_PMULL2_VEC Q9 Q11 Q20 64 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x6e301e31;       (* arm_EOR_VEC Q17 Q17 Q16 128 *)
  0x6e321d08;       (* arm_EOR_VEC Q8 Q8 Q18 128 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x0ef6e156;       (* arm_PMULL_VEC Q22 Q10 Q22 64 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xce1d2631;       (* arm_EOR3 Q17 Q17 Q29 Q9 *)
  0x4eca297d;       (* arm_TRN1 Q29 Q11 Q10 64 128 *)
  0x4eca696a;       (* arm_TRN2 Q10 Q11 Q10 64 128 *)
  0x4ef8e112;       (* arm_PMULL2_VEC Q18 Q8 Q24 64 *)
  0x0ef4e174;       (* arm_PMULL_VEC Q20 Q11 Q20 64 *)
  0x6e371e73;       (* arm_EOR_VEC Q19 Q19 Q23 128 *)
  0x0ef8e118;       (* arm_PMULL_VEC Q24 Q8 Q24 64 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xce165273;       (* arm_EOR3 Q19 Q19 Q22 Q20 *)
  0x3dc000d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 0)) *)
  0x3dc008d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 32)) *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x6e381e52;       (* arm_EOR_VEC Q18 Q18 Q24 128 *)
  0x6e3d1d4a;       (* arm_EOR_VEC Q10 Q10 Q29 128 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4ef5e15d;       (* arm_PMULL2_VEC Q29 Q10 Q21 64 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x0ef5e155;       (* arm_PMULL_VEC Q21 Q10 Q21 64 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0xad436d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&96))) *)
  0x3dc00cd7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 48)) *)
  0x3dc014d9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 80)) *)
  0x4e2009ef;       (* arm_REV64_VEC Q15 Q15 8 *)
  0x4e2009ad;       (* arm_REV64_VEC Q13 Q13 8 *)
  0xce157652;       (* arm_EOR3 Q18 Q18 Q21 Q29 *)
  0x4ecc29b0;       (* arm_TRN1 Q16 Q13 Q12 64 128 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4ef9e188;       (* arm_PMULL2_VEC Q8 Q12 Q25 64 *)
  0x4ef7e1aa;       (* arm_PMULL2_VEC Q10 Q13 Q23 64 *)
  0x0ef9e199;       (* arm_PMULL_VEC Q25 Q12 Q25 64 *)
  0x4ecc69ac;       (* arm_TRN2 Q12 Q13 Q12 64 128 *)
  0x0ef7e1b7;       (* arm_PMULL_VEC Q23 Q13 Q23 64 *)
  0x4ece29ed;       (* arm_TRN1 Q13 Q15 Q14 64 128 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4ef6e1cb;       (* arm_PMULL2_VEC Q11 Q14 Q22 64 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xad44697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&128))) *)
  0x0ef6e1d6;       (* arm_PMULL_VEC Q22 Q14 Q22 64 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0xce082a31;       (* arm_EOR3 Q17 Q17 Q8 Q10 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4ece69ee;       (* arm_TRN2 Q14 Q15 Q14 64 128 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x6e301d8c;       (* arm_EOR_VEC Q12 Q12 Q16 128 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x6e2d1dce;       (* arm_EOR_VEC Q14 Q14 Q13 128 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4ef8e190;       (* arm_PMULL2_VEC Q16 Q12 Q24 64 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x0ef8e198;       (* arm_PMULL_VEC Q24 Q12 Q24 64 *)
  0x4ef4e1ec;       (* arm_PMULL2_VEC Q12 Q15 Q20 64 *)
  0x4ef5e1cd;       (* arm_PMULL2_VEC Q13 Q14 Q21 64 *)
  0x0ef5e1d5;       (* arm_PMULL_VEC Q21 Q14 Q21 64 *)
  0x0ef4e1f4;       (* arm_PMULL_VEC Q20 Q15 Q20 64 *)
  0xad45717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&160))) *)
  0xce195e73;       (* arm_EOR3 Q19 Q19 Q25 Q23 *)
  0xce184252;       (* arm_EOR3 Q18 Q18 Q24 Q16 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0xce0b3231;       (* arm_EOR3 Q17 Q17 Q11 Q12 *)
  0xce165273;       (* arm_EOR3 Q19 Q19 Q22 Q20 *)
  0xfd400150;       (* arm_LDR D16 X10 (Immediate_Offset (word 0)) *)
  0xce153652;       (* arm_EOR3 Q18 Q18 Q21 Q13 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xce114e52;       (* arm_EOR3 Q18 Q18 Q17 Q19 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0xad466d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&192))) *)
  0x6e114235;       (* arm_EXT Q21 Q17 Q17 64 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x0ef0e23d;       (* arm_PMULL_VEC Q29 Q17 Q16 64 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xce1d5652;       (* arm_EOR3 Q18 Q18 Q29 Q21 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x0ef0e251;       (* arm_PMULL_VEC Q17 Q18 Q16 64 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x3dc0397c;       (* arm_LDR Q28 X11 (Immediate_Offset (word 224)) *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x6e124255;       (* arm_EXT Q21 Q18 Q18 64 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0xce154673;       (* arm_EOR3 Q19 Q19 Q21 Q17 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x6e134270;       (* arm_EXT Q16 Q19 Q19 64 *)
  0xcb000085;       (* arm_SUB X5 X4 X0 *)
  0xf101c0bf;       (* arm_CMP X5 (rvalue (word 112)) *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0xad4564d8;       (* arm_LDP Q24 Q25 X6 (Immediate_Offset (iword (&160))) *)
  0x4ebc1f9d;       (* arm_MOV_VEC Q29 Q28 128 *)
  0xad4354d4;       (* arm_LDP Q20 Q21 X6 (Immediate_Offset (iword (&96))) *)
  0xce00752c;       (* arm_EOR3 Q12 Q9 Q0 Q29 *)
  0xad445cd6;       (* arm_LDP Q22 Q23 X6 (Immediate_Offset (iword (&128))) *)
  0x540005ec;       (* arm_BGT (word 188) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea41c85;       (* arm_MOV_VEC Q5 Q4 128 *)
  0x4ea31c64;       (* arm_MOV_VEC Q4 Q3 128 *)
  0x0f00e413;       (* arm_MOVI D19 (word 0) *)
  0x0f00e411;       (* arm_MOVI D17 (word 0) *)
  0x0f00e412;       (* arm_MOVI D18 (word 0) *)
  0x4ea21c43;       (* arm_MOV_VEC Q3 Q2 128 *)
  0xf10180bf;       (* arm_CMP X5 (rvalue (word 96)) *)
  0x4ea11c22;       (* arm_MOV_VEC Q2 Q1 128 *)
  0x540005ec;       (* arm_BGT (word 188) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea41c85;       (* arm_MOV_VEC Q5 Q4 128 *)
  0xf10140bf;       (* arm_CMP X5 (rvalue (word 80)) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea31c64;       (* arm_MOV_VEC Q4 Q3 128 *)
  0x4ea11c23;       (* arm_MOV_VEC Q3 Q1 128 *)
  0x540006ac;       (* arm_BGT (word 212) *)
  0xf10100bf;       (* arm_CMP X5 (rvalue (word 64)) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea41c85;       (* arm_MOV_VEC Q5 Q4 128 *)
  0x4ea11c24;       (* arm_MOV_VEC Q4 Q1 128 *)
  0x540007ac;       (* arm_BGT (word 244) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0xf100c0bf;       (* arm_CMP X5 (rvalue (word 48)) *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea11c25;       (* arm_MOV_VEC Q5 Q1 128 *)
  0x540008ac;       (* arm_BGT (word 276) *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0xf10080bf;       (* arm_CMP X5 (rvalue (word 32)) *)
  0x4ea11c26;       (* arm_MOV_VEC Q6 Q1 128 *)
  0x54000a0c;       (* arm_BGT (word 320) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea11c27;       (* arm_MOV_VEC Q7 Q1 128 *)
  0xf10040bf;       (* arm_CMP X5 (rvalue (word 16)) *)
  0x54000b6c;       (* arm_BGT (word 364) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x14000069;       (* arm_B (word 420) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x6e084712;       (* arm_INS Q18 Q24 0 64 64 128 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08451b;       (* arm_INS Q27 Q8 0 64 64 128 *)
  0xce01752c;       (* arm_EOR3 Q12 Q9 Q1 Q29 *)
  0x4ef9e111;       (* arm_PMULL2_VEC Q17 Q8 Q25 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x0ef9e113;       (* arm_PMULL_VEC Q19 Q8 Q25 64 *)
  0x0ef2e372;       (* arm_PMULL_VEC Q18 Q27 Q18 64 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x6e08451b;       (* arm_INS Q27 Q8 0 64 64 128 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x4ef7e11c;       (* arm_PMULL2_VEC Q28 Q8 Q23 64 *)
  0x0ef7e11a;       (* arm_PMULL_VEC Q26 Q8 Q23 64 *)
  0xce02752c;       (* arm_EOR3 Q12 Q9 Q2 Q29 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x0ef8e37b;       (* arm_PMULL_VEC Q27 Q27 Q24 64 *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x4ef6e11c;       (* arm_PMULL2_VEC Q28 Q8 Q22 64 *)
  0x6e08451b;       (* arm_INS Q27 Q8 0 64 64 128 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x0ef6e11a;       (* arm_PMULL_VEC Q26 Q8 Q22 64 *)
  0x6e18077b;       (* arm_INS Q27 Q27 64 0 64 64 *)
  0x4ef5e37b;       (* arm_PMULL2_VEC Q27 Q27 Q21 64 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0xce03752c;       (* arm_EOR3 Q12 Q9 Q3 Q29 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08451b;       (* arm_INS Q27 Q8 0 64 64 128 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x0ef4e11a;       (* arm_PMULL_VEC Q26 Q8 Q20 64 *)
  0x4ef4e11c;       (* arm_PMULL2_VEC Q28 Q8 Q20 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x0ef5e37b;       (* arm_PMULL_VEC Q27 Q27 Q21 64 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0xce04752c;       (* arm_EOR3 Q12 Q9 Q4 Q29 *)
  0x3dc014d9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 80)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x6e08451b;       (* arm_INS Q27 Q8 0 64 64 128 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0xce05752c;       (* arm_EOR3 Q12 Q9 Q5 Q29 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x6e18077b;       (* arm_INS Q27 Q27 64 0 64 64 *)
  0x0ef9e11a;       (* arm_PMULL_VEC Q26 Q8 Q25 64 *)
  0x4ef9e11c;       (* arm_PMULL2_VEC Q28 Q8 Q25 64 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x4ef8e37b;       (* arm_PMULL2_VEC Q27 Q27 Q24 64 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3dc00cd7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 48)) *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08451b;       (* arm_INS Q27 Q8 0 64 64 128 *)
  0x0ef7e11a;       (* arm_PMULL_VEC Q26 Q8 Q23 64 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0xce06752c;       (* arm_EOR3 Q12 Q9 Q6 Q29 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x0ef8e37b;       (* arm_PMULL_VEC Q27 Q27 Q24 64 *)
  0x4ef7e11c;       (* arm_PMULL2_VEC Q28 Q8 Q23 64 *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08451b;       (* arm_INS Q27 Q8 0 64 64 128 *)
  0x3dc008d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 32)) *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x0ef6e11a;       (* arm_PMULL_VEC Q26 Q8 Q22 64 *)
  0x6e18077b;       (* arm_INS Q27 Q27 64 0 64 64 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0xce07752c;       (* arm_EOR3 Q12 Q9 Q7 Q29 *)
  0x4ef6e11c;       (* arm_PMULL2_VEC Q28 Q8 Q22 64 *)
  0x4ef5e37b;       (* arm_PMULL2_VEC Q27 Q27 Q21 64 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x6e200bde;       (* arm_REV32_VEC Q30 Q30 8 *)
  0x3d80021e;       (* arm_STR Q30 X16 (Immediate_Offset (word 0)) *)
  0x3dc000d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 0)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e084510;       (* arm_INS Q16 Q8 0 64 64 128 *)
  0x4ef4e11c;       (* arm_PMULL2_VEC Q28 Q8 Q20 64 *)
  0x2e281e10;       (* arm_EOR_VEC Q16 Q16 Q8 64 *)
  0x0ef4e11a;       (* arm_PMULL_VEC Q26 Q8 Q20 64 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x0ef5e210;       (* arm_PMULL_VEC Q16 Q16 Q21 64 *)
  0x6e301e52;       (* arm_EOR_VEC Q18 Q18 Q16 128 *)
  0xfd400150;       (* arm_LDR D16 X10 (Immediate_Offset (word 0)) *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x0ef0e235;       (* arm_PMULL_VEC Q21 Q17 Q16 64 *)
  0x6e331e2e;       (* arm_EOR_VEC Q14 Q17 Q19 128 *)
  0x6e114231;       (* arm_EXT Q17 Q17 Q17 64 *)
  0x4c00704c;       (* arm_STR Q12 X2 No_Offset *)
  0x6e2e1e52;       (* arm_EOR_VEC Q18 Q18 Q14 128 *)
  0x6e351e35;       (* arm_EOR_VEC Q21 Q17 Q21 128 *)
  0x6e351e52;       (* arm_EOR_VEC Q18 Q18 Q21 128 *)
  0x0ef0e251;       (* arm_PMULL_VEC Q17 Q18 Q16 64 *)
  0x6e124252;       (* arm_EXT Q18 Q18 Q18 64 *)
  0x6e311e73;       (* arm_EOR_VEC Q19 Q19 Q17 128 *)
  0x6e321e73;       (* arm_EOR_VEC Q19 Q19 Q18 128 *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e200a73;       (* arm_REV64_VEC Q19 Q19 8 *)
  0x4c007073;       (* arm_STR Q19 X3 No_Offset *)
  0xaa0903e0;       (* arm_MOV X0 X9 *)
  0x6d412fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d4237ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d433fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x6cc527e8;       (* arm_LDP D8 D9 SP (Postimmediate_Offset (iword (&80))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0x52800000;       (* arm_MOV W0 (rvalue (word 0)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let AESV8_GCM_8X_DEC_256_WB_EXEC = ARM_MK_EXEC_RULE aesv8_gcm_8x_dec_256_wb_mc;;

(* ------------------------------------------------------------------------- *)
(* JRH-style shared statement/capture machinery.                              *)
(* ------------------------------------------------------------------------- *)

(* The machine\'s 14-round aese/aesmc keystream tower XOR (k14 xor cph) equals
   the spec keystream XOR: proved ONCE, so every per-block plaintext capture is
   a rewrite (replaces the per-site aes256_encrypt unfold + WORD_BLAST). *)
let AES256_XOR_ENCRYPT_RECONSTRUCT = prove
 (`!ctr cph k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14:int128.
    word_xor
     (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese
       (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc
       (aese ctr k0) ) k1) ) k2) ) k3) ) k4) ) k5) ) k6) ) k7) ) k8) ) k9) ) k10) ) k11) ) k12) ) k13)
     (word_xor k14 cph) =
    word_xor cph (aes256_encrypt ctr [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
  REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC WORD_BLAST);;

(* The named 13-round partial tower (the keystream register shape at the
   shared-front seam s265: rounds 0..12 + the final aese, NO 14th-key xor --
   that xor happens per-block in the tail eor3).  Naming it collapses the 8
   front-postcondition Q towers from ~2.6k chars each to one application, and
   the reconstruct lemma below keeps every tail capture site working on the
   folded form. *)
let aes13 = new_definition
 `aes13 (p:int128) (k0:int128) (k1:int128) (k2:int128) (k3:int128) (k4:int128)
        (k5:int128) (k6:int128) (k7:int128) (k8:int128) (k9:int128) (k10:int128)
        (k11:int128) (k12:int128) (k13:int128) : int128 =
    aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese
      (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc
      (aese p k0) ) k1) ) k2) ) k3) ) k4) ) k5) ) k6) ) k7) ) k8) ) k9) ) k10) ) k11) ) k12) ) k13`;;

(* All tail capture sites rewrite with GSYM of this; rebinding it over aes13
   keeps them verbatim while the front postcondition stays folded. *)
let AES256_XOR_ENCRYPT_RECONSTRUCT =
  REWRITE_RULE[GSYM aes13] AES256_XOR_ENCRYPT_RECONSTRUCT;;

(* The 12-slot aws-lc htable layout as one predicate over the abstract GHASH
   input key h (slot values = the byteswapped polyval_dot towers + packed
   karatsuba mids, exactly the per-slot hypotheses of the masked-band chain).
   JRH htable_mem_4 pattern.  EXPAND (REWRITE_TAC[htable_mem_dec] + let_CONV)
   BEFORE stepping so the htable loads resolve (fast_tail lesson). *)
let htable_mem_dec = new_definition
 `htable_mem_dec (h:int128) (ptr:int64) (s:armstate) <=>
    let hb = byteswap128 h in
    let h2 = byteswap128 (polyval_dot hb hb) in
    let h3 = byteswap128 (polyval_dot (polyval_dot hb hb) hb) in
    let h4 = byteswap128 (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) in
    let h5 = byteswap128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) hb) in
    let h6 = byteswap128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) hb) hb) in
    let h7 = byteswap128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) hb) hb) hb) in
    let h8 = byteswap128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) hb) hb) hb) hb) in
    read (memory :> bytes128 ptr) s = h /\
    read (memory :> bytes128 (word_add ptr (word 16))) s =
      word_join (karatsuba_mid h2) (karatsuba_mid h) /\
    read (memory :> bytes128 (word_add ptr (word 32))) s = h2 /\
    read (memory :> bytes128 (word_add ptr (word 48))) s = h3 /\
    read (memory :> bytes128 (word_add ptr (word 64))) s =
      word_join (karatsuba_mid h4) (karatsuba_mid h3) /\
    read (memory :> bytes128 (word_add ptr (word 80))) s = h4 /\
    read (memory :> bytes128 (word_add ptr (word 96))) s = h5 /\
    read (memory :> bytes128 (word_add ptr (word 112))) s =
      word_join (karatsuba_mid h6) (karatsuba_mid h5) /\
    read (memory :> bytes128 (word_add ptr (word 128))) s = h6 /\
    read (memory :> bytes128 (word_add ptr (word 144))) s = h7 /\
    read (memory :> bytes128 (word_add ptr (word 160))) s =
      word_join (karatsuba_mid h8) (karatsuba_mid h7) /\
    read (memory :> bytes128 (word_add ptr (word 176))) s = h8`;;

(* ------------------------------------------------------------------------- *)
(* Guard-abort theorem: the whole-blocks contract is enforced.  For nonzero    *)
(* bit_len not a multiple of 128 the function returns 0 via the entry guard    *)
(* (cbz/tst/b.ne -> mov w0,#0; ret), modifying no memory and no callee-saved   *)
(* state (the guard fires before the d8-d15 saves).                            *)
(* ------------------------------------------------------------------------- *)

let AESV8_GCM_8X_DEC_256_WB_GUARD = prove
 (`!pc in_p bit_len out_p xi_p ivec_p key_p htbl_p returnaddress.
    ~(val bit_len = 0) /\ ~(val bit_len MOD 128 = 0)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
           read PC s = word pc /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [in_p; bit_len; out_p; xi_p; ivec_p; key_p; htbl_p] s)
      (\s. read PC s = returnaddress /\
           C_RETURN s = word 0)
      MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(REWRITE_RULE[C_ARGUMENTS]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (1--2) THEN
  SUBGOAL_THEN `~(val (word_and (bit_len:int64) (word 127)) = 0)` ASSUME_TAC THENL
   [SUBGOAL_THEN `127 = 2 EXP 7 - 1` SUBST1_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 EXP 7 = 128`]; ALL_TAC] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (3--6) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Shared band machinery (KEEPGH stepper + the Q19 byte-reversed-xi identity).*)
(* ------------------------------------------------------------------------- *)


(* KEEPGH stepper (copied from le8block.ml; wb.ml does not load le8block) *)
let DISCARD_OLDSTATE_KEEPGH_TAC s =
  let v = mk_var(s,`:armstate`) in
  let rec unbound_statevars_of_read bound tm = match tm with
      Comb(Comb(Const("read",_),_),st) -> if mem st bound then [] else [st]
    | Comb(a,b) -> union (unbound_statevars_of_read bound a) (unbound_statevars_of_read bound b)
    | Abs(vv,t) -> unbound_statevars_of_read (vv::bound) t | _ -> [] in
  let rec mentions_ghreg t = match t with
      Comb(Comb(Const("read",_),cmp),_) ->
        (match cmp with Const(n,_) -> n="Q16"||n="Q17"||n="Q18"||n="Q19" | _ -> false)
    | Comb(a,b) -> mentions_ghreg a || mentions_ghreg b | Abs(_,t2) -> mentions_ghreg t2 | _ -> false in
  DISCARD_ASSUMPTIONS_TAC(fun thm ->
    if mentions_ghreg (concl thm) then false else
    let us = unbound_statevars_of_read [] (concl thm) in
    if us = [] || us = [v] then false else if not(mem v us) then true else true);;
let ARM_STEPS_FOLD_KEEPGH_TAC exec snums =
  MAP_EVERY (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN GCM_SIMD_SIMPLIFY_TAC THEN
              DISCARD_OLDSTATE_KEEPGH_TAC s THEN CLARIFY_TAC) (statenames "s" snums);;

(* The byte-reversed-xi identity: the machine's ldr/ext/rev64 (steps ~180-189)
   leave Q19 in word_join(reversefields lo)(reversefields hi) form; this equals
   word_bytereverse of the whole 128-bit xi.  Rewriting Q19 to this clean atom
   right after step 189 is what lets the tail's GHASH accumulator close against
   the postcondition's word_bytereverse xi. *)
let Q19_BREVXI = prove
 (`word_join (word_reversefields 8 (word_subword (xi:int128) (0,64):int64))
             (word_reversefields 8 (word_subword xi (64,64):int64)):int128 =
   word_bytereverse xi`,
  CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* AESV8_GCM_8X_DEC_256_WB_1BLOCK: the whole-blocks dec variant, bit_len=128. *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(*     Shared inter-band machinery (bridge closers, spec folds, steppers)    *)
(* ------------------------------------------------------------------------- *)



(* ------------------------------------------------------------------------- *)
(* The WB 2-block bridge close: DEC_2BLK_GMULT2_BRIDGE_TAC (core.ml) with
   karatsuba_mid unfolded first (htable_mem_dec presents the hk slot as
   word_join (karatsuba_mid h2) (karatsuba_mid h); the merge needs the
   expanded subword form to pair machine mids with spec mids). *)
let WB2_GMULT2_BRIDGE_TAC : tactic =
  let a0t = `word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`
  and a1t = `word_bytereverse cph1:int128` in
  let gmult2_dec = REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [a0t; `byteswap128 h2:int128`; a1t; `byteswap128 h:int128`] GMULT2_FULL_CORRECT_BA) in
  let r1def = `word_xor (word_xor (word_shl (word_zx (wal:64 word):128 word) 63) (word_shl (word_zx wal:128 word) 62)) (word_shl (word_zx wal:128 word) 57)` in
  let udef = `word_xor (word_subword (r1:128 word) (0,64):64 word) (word_xor (word_xor qq1h qq6h) (word_xor (word_xor qq0l (word_xor qq1l qq4l)) (word_xor qq5l (word_xor qq10l qq6l))))` in
  FIRST_ASSUM(fun th ->
    if (try lhs(concl th)=`byteswap128 h2` with _->false)
    then GEN_REWRITE_TAC RAND_CONV
           [REWRITE_RULE[GSYM gmult2_dec]
             (GEN_REWRITE_RULE (RAND_CONV o ONCE_DEPTH_CONV) [GSYM th]
               (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
                       `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`]
                 GHASH_POLYVAL_ACC_2))]
    else NO_TAC) THEN
  REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  REWRITE_TAC[byteswap128] THEN
  REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
  REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
  REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
  REWRITE_TAC[karatsuba_mid] THEN
  ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
  REWRITE_TAC[PMUL_W_64_128] THEN REWRITE_TAC[JOINMID] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  EVERY (map (fun a ->
    let av = mk_var(a,`:int128`) in
    ABBREV_TAC (mk_eq(mk_var(a^"l",`:64 word`), mk_comb(mk_comb(`word_subword:int128->num#num->64 word`, av), `(0,64)`))) THEN
    ABBREV_TAC (mk_eq(mk_var(a^"h",`:64 word`), mk_comb(mk_comb(`word_subword:int128->num#num->64 word`, av), `(64,64)`))))
    ["qq0";"qq1";"qq4";"qq5";"qq6";"qq10"]) THEN
  ABBREV_TAC `wal:64 word = word_xor qq1l qq6l` THEN
  REWRITE_TAC[DEC2_WXSYM] THEN
  FIRST_ASSUM(fun th -> if (try rhs(concl th)=`wal:64 word` && lhs(concl th)=`word_xor qq1l qq6l:64 word` with _->false) then REWRITE_TAC[th] else NO_TAC) THEN
  ABBREV_TAC (mk_eq(`r1:128 word`, r1def)) THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_subword (word_shl (word_zx (wal:64 word):128 word) 63) (0,64):64 word) (word_subword (word_shl (word_zx wal:128 word) 62) (0,64):64 word)) (word_subword (word_shl (word_zx wal:128 word) 57) (0,64):64 word) = word_subword (r1:128 word) (0,64):64 word`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_subword (word_shl (word_zx (wal:64 word):128 word) 63) (64,64):64 word) (word_subword (word_shl (word_zx wal:128 word) 62) (64,64):64 word)) (word_subword (word_shl (word_zx wal:128 word) 57) (64,64):64 word) = word_subword (r1:128 word) (64,64):64 word`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_subword (word_shl (word_zx (wal:64 word):128 word) 57) (0,64):64 word) (word_xor (word_subword (word_shl (word_zx wal:128 word) 62) (0,64):64 word) (word_subword (word_shl (word_zx wal:128 word) 63) (0,64):64 word)) = word_subword (r1:128 word) (0,64):64 word`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_subword (word_shl (word_zx (wal:64 word):128 word) 57) (64,64):64 word) (word_xor (word_subword (word_shl (word_zx wal:128 word) 62) (64,64):64 word) (word_subword (word_shl (word_zx wal:128 word) 63) (64,64):64 word)) = word_subword (r1:128 word) (64,64):64 word`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  ABBREV_TAC (mk_eq(`u:64 word`, udef)) THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_xor qq10l qq4l) (word_xor wal (word_xor qq0l qq5l))) (word_xor (word_xor qq1h qq6h) (word_subword (r1:128 word) (0,64):64 word)) = u`
   (fun th -> REWRITE_TAC[th]) THENL [MAP_EVERY EXPAND_TAC ["u";"wal"] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_subword (r1:128 word) (0,64):64 word) (word_xor (word_xor qq1h qq6h) (word_xor (word_xor qq0l (word_xor qq1l qq4l)) (word_xor qq5l (word_xor qq10l qq6l)))) = u`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "u" THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC `us57:128 word = word_shl (word_zx (u:64 word):128 word) 57` THEN
  ABBREV_TAC `us62:128 word = word_shl (word_zx (u:64 word):128 word) 62` THEN
  ABBREV_TAC `us63:128 word = word_shl (word_zx (u:64 word):128 word) 63` THEN
  GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN LANE_CLOSE_TAC;;

(* ------------------------------------------------------------------------- *)
(* AESV8_GCM_8X_DEC_256_WB_2BLOCK: whole-blocks dec variant, bit_len=256.     *)
(* ------------------------------------------------------------------------- *)



(* ========================================================================= *)
(* WB_3BLOCK .. WB_8BLOCK: whole-blocks dec variant, bit_len = 128*N (N=3..8).*)
(* Promoted from work.ml (proved interactively; hyps=0, axioms=3, no cheats). *)
(* Shared N>=3 band machinery (ported from le3block.ml) precedes the theorems.*)
(* ========================================================================= *)

(* ============================================================================
   WB_3BLOCK: PROVED interactively (hyps=0, axioms=3).  Full script below.

   CASCADE STEP MAP (from the b.gt chain disassembly; band N takes the
   #16*(N-1) branch; cascade always starts ARM_STEPS_RESOLVE_TAC (266--277)
   then (278--sEnd)):
     N=2: sEnd=313 -> pc+4348 (R1)   N=3: sEnd=309 -> pc+4288 (R2)
     N=4: sEnd=303 -> pc+4220 (R3)   N=5: sEnd=297 -> pc+4164 (R4)
     N=6: sEnd=290 -> pc+4104 (R5)   N=7: sEnd=282 -> pc+4048 (R6)
     N=8: sEnd=270 -> pc+4000 (R7)
   Front keystream discard lists: keep Q0..Q(N-1):
     per-step 6..30:  mk_discard2 [N..7]        (N=8: [])
     bulk windows:    mk_discard2 [N..7]@[30]   (N=8: [30])
     after 256-265:   mk_discard2 [N..7 minus the moved one]@[30] — for N=2 it
     was [2;3;4;5;6;30]; for N=3 [3;4;5;6;30]; pattern: drop 7 keep 30.
   Block-i keystream after cascade movs: block-0 in Q0, block-(N-1) in Q7,
   block-i (0<i<N-1) in Q(8-N+i).
   WB_3BLOCK tail map (entry s309=pc+4288 R2):
     310-315 KEEPGH; Q12 s315 = block-0 PT (reconstruct+WORD_RULE).
     s316 = str q12 (VSTEPS_FOLD ok here) + carry out_p readback + KEEPGH-discard.
     317-330 KEEPGH (317 = eor3 block-1 vs Q6); Q12 s330 capture via
       GCM_CTR_INC_LANES (do the capture at s330, right before its store).
     s331 = str block-1 (VSTEPS_FOLD ok) + carry out_p AND out_p+16 + discard.
     332-336 KEEPGH (336 = eor3 block-2 vs Q7); Q12 s336 capture via
       GCM_CTR_INC2_LANES.
     337-358 KEEPGH -> s358 pc+4484.
     s359 = str block-2 (PLAIN ARM_VSTEPS_TAC — FOLD chokes) + carry all 3
       out_p readbacks + KEEPGH-discard + 3x DISCH.
     360-366 KEEPGH -> s366 pc+4516 = BRIDGE (post eor v19,v19,v18).
     BRIDGE: SUBGOAL read Q19 s366 = ghash_polyval_acc .. [brev cph0;cph1;cph2],
       close = spec fold (spec_to_byteform_wb3 h2asm h3asm + GSYM gmult3_dec)
       THEN the WB2-style rewrites incl. REWRITE_TAC[karatsuba_mid] THEN
       ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN QQ8_FOLD_TAC THEN
       WA_UNIFY_TAC THEN WV_UNIFY_TAC THEN ABBREV_WAWV_TAC THEN
       subword/QQ0SPLIT/JOIN_EQ_SPLIT THEN CONJ_TAC THEN LANE_FINISH_TAC.
       (NO FOLD_MID_HPOW needed at N=3: QQ8_FOLD grabs the one H2-keyed mid;
       the H3-keyed karatsuba_mid h3 mid merged already because karatsuba_mid
       was unfolded.  For N>=4 expect FOLD_MID_HPOW "H<k>" for k=N-1..2 as in
       le4-8, called BETWEEN MERGE and WA_UNIFY.)
     367-368 ext/rev64 + Q19 s368 = brev gval (WORD_BLAST); 369 tag store
       (plain VSTEPS); DISCARD_COUNTER_ONLY; FINAL + MAYCHANGE as WB_2BLOCK.
   ============================================================================ *)

(* ---- shared N>=3 band machinery (ported from le3block.ml; wb chain does
   not load the le bands) ---- *)
let collect_pmuls p t = let rec collect t acc = let acc = if p t then t::acc else acc in
  match t with Comb(a,b)->collect a (collect b acc)|Abs(_,b)->collect b acc|_->acc in setify(collect t []);;
let isWpmul t = try fst(dest_const(repeat rator t))="word_pmul" && rand t=`word 13979173243358019584:64 word` with _->false;;
let SJ_COLLAPSE = prove
 (`!w:128 word. word_subword (word_subword (word_join w w:256 word) (64,128):128 word) (0,64):64 word
                = word_subword w (64,64)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;
let SJ_COLLAPSE2 = prove
 (`!w:128 word. word_subword (word_subword (word_join w w:256 word) (64,128):128 word) (64,64):64 word
                = word_subword w (0,64)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;
let word_xor_left_comm = WORD_RULE `word_xor (a:64 word) (word_xor b c) = word_xor b (word_xor a c)`;;
let xor_pair_comm = WORD_RULE `word_xor (a:64 word) b = word_xor b a`;;
let term_leq t1 t2 = String.compare (string_of_term t1) (string_of_term t2) <= 0;;
let rec bubble_conv tm = match tm with
  | Comb(Comb(Const("word_xor",_), a), b) ->
    (match b with
     | Comb(Comb(Const("word_xor",_), b1), _) ->
       if term_leq a b1 then AP_TERM (mk_comb(rator(rator tm), a)) (bubble_conv b)
       else let th1 = PART_MATCH lhs word_xor_left_comm tm in
         let new_rhs = rhs(concl th1) in TRANS th1 (AP_TERM (rator new_rhs) (bubble_conv (rand new_rhs)))
     | _ -> if term_leq a b then REFL tm else PART_MATCH lhs xor_pair_comm tm)
  | _ -> REFL tm;;
let rec bubble_sort_conv tm =
  let rec count_xors t = match t with Comb(Comb(Const("word_xor",_), _), r) -> 1 + count_xors r | _ -> 0 in
  let n = count_xors tm in
  let rec apply_n_times k acc = if k <= 0 then acc else apply_n_times (k-1) (TRANS acc (bubble_conv (rhs(concl acc)))) in
  apply_n_times n (REFL tm);;
let rec bubble_fix tm = let th = bubble_sort_conv tm in let r = rhs(concl th) in
  if r = tm then th else TRANS th (bubble_fix r);;
let LANE_FINISH_TAC : tactic =
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  CONV_TAC(RAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[SJ_COLLAPSE; SJ_COLLAPSE2] THEN REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(BINOP_CONV bubble_fix) THEN REFL_TAC;;
let WA_UNIFY_TAC : tactic = fun (asl,w) ->
  let l=lhs w and r=rhs w in
  let iswa t = isWpmul t && not(can (find_term (fun u->u<>t && isWpmul u)) (rand(rator t))) in
  let lwa=hd(collect_pmuls iswa l) and rwa=hd(collect_pmuls iswa r) in
  if lwa=rwa then ALL_TAC (asl,w) else
  let wa_eq = prove(mk_eq(rwa,lwa), MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_RULE) in
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [wa_eq] (asl,w);;
let WV_UNIFY_TAC : tactic = fun (asl,w) ->
  let l=lhs w and r=rhs w in
  let iswv t = isWpmul t && (can (find_term (fun u->u<>t && isWpmul u)) (rand(rator t))) in
  let lwv=hd(collect_pmuls iswv l) and rwv=hd(collect_pmuls iswv r) in
  if lwv=rwv then ALL_TAC (asl,w) else
  let in_eq = BITBLAST_RULE (mk_eq(rand(rator rwv), rand(rator lwv))) in
  let wv_eq = AP_THM (AP_TERM `word_pmul:64 word->64 word->128 word` in_eq) `word 13979173243358019584:64 word` in
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [wv_eq] (asl,w);;
let ABBREV_WAWV_TAC : tactic = fun (asl,w) ->
  let l=lhs w in
  let iswa t = isWpmul t && not(can (find_term (fun u->u<>t && isWpmul u)) (rand(rator t))) in
  let lwa=hd(collect_pmuls iswa l) in
  (ABBREV_TAC (mk_eq(`WAz:128 word`, lwa)) THEN
   (fun (asl,w) -> let l=lhs w in
     (match collect_pmuls isWpmul l with wv::_ -> ABBREV_TAC (mk_eq(`WVz:128 word`, wv)) | [] -> ALL_TAC) (asl,w)))
  (asl,w);;
let pmul_mult_hpow t =
  let m = rand t in
  if can(find_term(fun u->u=`h2:int128`)) m then "H2" else
  if can(find_term(fun u->u=`h3:int128`)) m then "H3" else
  if can(find_term(fun u->u=`h4:int128`)) m then "H4" else
  if can(find_term(fun u->u=`h5:int128`)) m then "H5" else
  if can(find_term(fun u->u=`h6:int128`)) m then "H6" else
  if can(find_term(fun u->u=`h7:int128`)) m then "H7" else
  if can(find_term(fun u->u=`h8:int128`)) m then "H8" else
  if can(find_term(fun u->u=`h:int128`)) m then "H1" else
  if can(find_term(fun u->u=`word 13979173243358019584:64 word`)) m then "W" else "?";;
let is_pmul128_tm t = try fst(dest_const(repeat rator t))="word_pmul" && type_of t = `:128 word` with _->false;;
let WB_MID_FIX = [WORD_SUBWORD_INSERT_INNER; WORD_SUBWORD_INSERT_OUTER; INSERT_SUBWORD_KILL;
                  WORD_INSERT_SUBWORD; JOINMID; JOIN_SUBWORD_RULES; RF8_SUBWORD;
                  WORD_SUBWORD_SUBWORD; WORD_SUBWORD_XOR];;
let FOLD_MID_HPOW hp : tactic = fun (asl,w) ->
  let l = lhs w in
  let mid = hd(List.filter (fun t -> pmul_mult_hpow t = hp) (setify(find_terms is_pmul128_tm l))) in
  let cands = List.filter (fun (_,th) ->
      try let r=rhs(concl th) and lft=lhs(concl th) in
          is_var r && (let n=fst(dest_var r) in String.length n>=2 && String.sub n 0 2="qq") &&
          is_pmul128_tm lft && pmul_mult_hpow lft = hp
      with _->false) asl in
  let try_qq (_,th) =
    let qq = rhs(concl th) in
    (SUBGOAL_THEN (mk_eq(mid,qq)) (fun e->REWRITE_TAC[e]) THENL
      [GEN_REWRITE_TAC RAND_CONV [GSYM th] THEN
       MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN
       (CONV_TAC WORD_BLAST ORELSE (REWRITE_TAC WB_MID_FIX THEN CONV_TAC WORD_BLAST)); ALL_TAC]) in
  (FIRST (map try_qq cands)) (asl,w);;
let QQ8_FOLD_TAC : tactic = fun (asl,w) ->
  let l=lhs w in
  let ishpmul t=try fst(dest_const(repeat rator t))="word_pmul" && type_of t = `:128 word`
    && rand t <> `word 13979173243358019584:64 word`
    && can (find_term(fun u->u=`h2:int128`)) t && not(can (find_term(fun u->isWpmul u)) t) with _->false in
  let qq8th = snd(List.find(fun(_,th)->let c=concl th in is_eq c && (try rhs c=`qq8:128 word` with _->false)) asl) in
  (match collect_pmuls ishpmul l with
   | gp8t::_ -> (SUBGOAL_THEN (mk_eq(gp8t, `qq8:128 word`)) (fun th -> REWRITE_TAC[th]) THENL
      [GEN_REWRITE_TAC RAND_CONV [GSYM qq8th] THEN
       ((MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST) ORELSE
        (ONCE_REWRITE_TAC[WORD_PMUL_SYM] THEN MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST)); ALL_TAC])
   | [] -> ALL_TAC) (asl,w);;
let POLYVAL_DOT_SYM = prove
 (`!a b:int128. polyval_dot a b = polyval_dot b a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[polyval_dot] THEN AP_TERM_TAC THEN
  REWRITE_TAC[WORD_PMUL_SYM]);;
let GCM_CTR_INC2_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc ctr0)`,
        subst [`word 2:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;
let PACK3_ID, GMULT3_FULL_CORRECT_BA = build_GMULTn_fast 3;;
let spec_to_byteform_wb3 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2] =
       polyval_reduce_prop3
        (word_xor
         (word_xor
          (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h3))
          (word_pmul (word_bytereverse cph1) (byteswap128 h2)))
         (word_pmul (word_bytereverse cph2) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`;
            `word_bytereverse cph2:int128`] GHASH_POLYVAL_ACC_3)] THEN
  SUBGOAL_THEN `polyval_dot (byteswap128 h) (polyval_dot (byteswap128 h) (byteswap128 h)) = byteswap128 h3`
    (fun th -> REWRITE_TAC[th]) THENL
  [ONCE_REWRITE_TAC[POLYVAL_DOT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* AESV8_GCM_8X_DEC_256_WB_3BLOCK: whole-blocks dec variant, bit_len=384.     *)
(* ------------------------------------------------------------------------- *)
(* ---- shared merge machinery (originally introduced for the WB_8 bridge;
   moved up 2026-07-18 because the optimized WB_3..6 closes also use
   MERGE_ANY_TAC / MERGE_QQPAIR_KM_TAC).  See the WB_8 header note for the
   greedy-pairing story. ---- *)

let MERGE_ONE_ANY_TAC : tactic = fun (asl,w) ->
  let is_pmul t = try let (hd,a)=strip_comb t in fst(dest_const hd)="word_pmul" && List.length a=2 with _->false in
  let is_wordconst t = try is_comb t && fst(dest_const(rator t))="word" && is_numeral(rand t) with _->false in
  let is_keyvar n = String.length n>=2 && n.[0]='k' &&
                    (try let _ = int_of_string (String.sub n 1 (String.length n-1)) in true with _->false) in
  let goalvars = setify(map (fun t->fst(dest_var t))
    (find_terms (fun t->is_var t && type_of t=`:int128` &&
      (let n=fst(dest_var t) in String.length n>=2 && String.sub n 0 2="qq")) w)) in
  let defs = List.filter (fun (_,th)->let c=concl th in is_eq c && is_var(rhs c) &&
    is_pmul(lhs c) && mem (fst(dest_var(rhs c))) goalvars) asl in
  let fvnames t = sort (<) (List.filter (fun n -> not(is_keyvar n))
                              (map (fun v->fst(dest_var v)) (frees t))) in
  let lane_tag op2 =
    if is_comb op2 && is_comb(rator op2) &&
       (try fst(dest_const(rator(rator op2)))="word_subword" with _->false)
    then string_of_term(rand op2) else "X" in
  let info th =
    let p = lhs(concl th) in
    let (_,args) = strip_comb p in
    let op1 = el 0 args and op2 = el 1 args in
    (rhs(concl th), op2, (fvnames op1, fvnames op2, lane_tag op2)) in
  let items = map (fun (_,th)-> info th) defs in
  let rec allpairs_acc = function
    | [] -> []
    | (v,op2,sg)::rest ->
        let cands =
          if is_wordconst op2
          then List.filter (fun (v2,op2b,_)-> v2<>v && is_wordconst op2b && op2b=op2) rest
          else List.filter (fun (v2,op2b,sg2)-> v2<>v && not(is_wordconst op2b) && sg2=sg) rest in
        (map (fun (v2,_,_) -> (v,v2)) cands) @ allpairs_acc rest in
  let pairs = allpairs_acc items in
  if pairs = [] then failwith "MERGE_ONE_ANY_TAC: nothing to merge" else
  let close_op = FAST_OPERAND_TAC ORELSE CONV_TAC WORD_BLAST in
  let cand_tac (v1,v2) =
    SUBGOAL_THEN (mk_eq(v1,v2))
      (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th]))
     THENL [EXPAND_TAC(fst(dest_var v1)) THEN EXPAND_TAC(fst(dest_var v2)) THEN
            ((MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN close_op)
             ORELSE (GEN_REWRITE_TAC LAND_CONV [WORD_PMUL_SYM] THEN
                     MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN close_op));
            ALL_TAC] in
  FIRST (map cand_tac pairs) (asl,w);;
let MERGE_ANY_TAC : tactic = REPEAT MERGE_ONE_ANY_TAC;;
let MERGE_QQPAIR_TAC (n1:string) (n2:string) : tactic =
  SUBGOAL_THEN (mk_eq(mk_var(n1,`:128 word`), mk_var(n2,`:128 word`)))
    (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
  [EXPAND_TAC n1 THEN EXPAND_TAC n2 THEN
   ((MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN
     (CONV_TAC WORD_BLAST ORELSE (REWRITE_TAC WB_MID_FIX THEN CONV_TAC WORD_BLAST)))
    ORELSE (GEN_REWRITE_TAC LAND_CONV [WORD_PMUL_SYM] THEN
            MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN
            (CONV_TAC WORD_BLAST ORELSE (REWRITE_TAC WB_MID_FIX THEN CONV_TAC WORD_BLAST))));
   ALL_TAC];;

(* ---- WB_7/WB_8 stepping-optimization machinery (2026-07-18).
   The whole-blocks stores window used ARM_STEPS_FOLD_KEEPGH_TAC throughout,
   keeping all of Q16-Q19 alive across ~130 states: the per-step
   GCM_SIMD_SIMPLIFY pass rescans a linearly growing pile => O(n^2)
   (WB_7 1573s, WB_8 the worst; repeated 30GB OOM kills).  Fix mirrors
   le8block's KEEPQ18/midacc pattern + the per-step-discard memo:
   step the window keeping ONLY the LATEST read Q18 fact (the machine's
   carried GHASH mid; store readbacks self-propagate), atomize it as
   `midacc`, and let the bridge expand it once.  271-392: hundreds of
   seconds -> ~116s; whole WB_8 tail ~26min -> ~9min. ---- *)
let DISCARD_OLDSTATE_KEEPQ18_TAC s =
  let v = mk_var(s,`:armstate`) in
  let rec unbound_statevars_of_read bound tm = match tm with
      Comb(Comb(Const("read",_),_),st) -> if mem st bound then [] else [st]
    | Comb(a,b) -> union (unbound_statevars_of_read bound a) (unbound_statevars_of_read bound b)
    | Abs(vv,t) -> unbound_statevars_of_read (vv::bound) t | _ -> [] in
  let rec mentions_q18 t = match t with
      Comb(Comb(Const("read",_),cmp),_) ->
        (match cmp with Const(n,_) -> n="Q18" | _ -> false)
    | Comb(a,b) -> mentions_q18 a || mentions_q18 b | Abs(_,t2) -> mentions_q18 t2 | _ -> false in
  DISCARD_ASSUMPTIONS_TAC(fun thm ->
    if mentions_q18 (concl thm) then false else
    let us = unbound_statevars_of_read [] (concl thm) in
    if us = [] || us = [v] then false else true);;
let state_num_of_q18_fact th =
  try let c = concl th in
      if not(is_eq c) then None else
      match lhs c with
        Comb(Comb(Const("read",_),Const("Q18",_)),Var(sn,_)) when String.length sn > 1 && sn.[0]='s' ->
          Some(int_of_string(String.sub sn 1 (String.length sn - 1)))
      | _ -> None
  with _ -> None;;
let DISCARD_STALE_Q18_TAC : tactic = fun (asl,w) ->
  let nums = List.filter_map (fun (_,th) -> state_num_of_q18_fact th) asl in
  match nums with
  | [] | [_] -> ALL_TAC (asl,w)
  | _ -> let mx = List.fold_left max 0 nums in
         DISCARD_ASSUMPTIONS_TAC (fun th ->
           match state_num_of_q18_fact th with
           | Some k -> k < mx
           | None -> false) (asl,w);;
let ARM_STEPS_FOLD_Q18LATEST_TAC exec snums =
  MAP_EVERY (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN GCM_SIMD_SIMPLIFY_TAC THEN
              DISCARD_STALE_Q18_TAC THEN DISCARD_OLDSTATE_KEEPQ18_TAC s THEN CLARIFY_TAC)
    (statenames "s" snums);;
(* MERGE_QQPAIR / FOLD_MID_HPOW variants that unfold karatsuba_mid inside the
   closing WORD_BLAST: the midacc expansion exposes machine mids whose spec
   partners are karatsuba_mid-folded. *)
let MERGE_QQPAIR_KM_TAC (n1:string) (n2:string) : tactic =
  SUBGOAL_THEN (mk_eq(mk_var(n1,`:128 word`), mk_var(n2,`:128 word`)))
    (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
  [EXPAND_TAC n1 THEN EXPAND_TAC n2 THEN REWRITE_TAC[karatsuba_mid] THEN
   ((MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN
     (CONV_TAC WORD_BLAST ORELSE (REWRITE_TAC WB_MID_FIX THEN CONV_TAC WORD_BLAST)))
    ORELSE (GEN_REWRITE_TAC LAND_CONV [WORD_PMUL_SYM] THEN
            MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN
            (CONV_TAC WORD_BLAST ORELSE (REWRITE_TAC WB_MID_FIX THEN CONV_TAC WORD_BLAST))));
   ALL_TAC];;
let FOLD_MID_HPOW_KM hp : tactic = fun (asl,w) ->
  let l = lhs w in
  let mid = hd(List.filter (fun t -> pmul_mult_hpow t = hp) (setify(find_terms is_pmul128_tm l))) in
  let cands = List.filter (fun (_,th) ->
      try let r=rhs(concl th) and lft=lhs(concl th) in
          is_var r && (let n=fst(dest_var r) in String.length n>=2 && String.sub n 0 2="qq") &&
          is_pmul128_tm lft && pmul_mult_hpow lft = hp
      with _->false) asl in
  let try_qq (_,th) =
    let qq = rhs(concl th) in
    (SUBGOAL_THEN (mk_eq(mid,qq)) (fun e->REWRITE_TAC[e]) THENL
      [GEN_REWRITE_TAC RAND_CONV [GSYM th] THEN REWRITE_TAC[karatsuba_mid] THEN
       MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN
       (CONV_TAC WORD_BLAST ORELSE (REWRITE_TAC WB_MID_FIX THEN CONV_TAC WORD_BLAST)); ALL_TAC]) in
  (FIRST (map try_qq cands)) (asl,w);;
(* WA-unify via BITBLAST_RULE: stock WA_UNIFY_TAC's WORD_RULE stack-overflows
   on the ~1.1k-char wa inputs this state produces. *)
let WA_UNIFY_BB_TAC : tactic = fun (asl,w) ->
  let l=lhs w and r=rhs w in
  let iswa t = isWpmul t && not(can (find_term (fun u->u<>t && isWpmul u)) (rand(rator t))) in
  let lwa=hd(collect_pmuls iswa l) and rwa=hd(collect_pmuls iswa r) in
  if lwa=rwa then ALL_TAC (asl,w) else
  let in_eq = BITBLAST_RULE (mk_eq(rand(rator rwa), rand(rator lwa))) in
  let mult_eq = BITBLAST_RULE (mk_eq(rand rwa, rand lwa)) in
  let wa_eq = MATCH_MP (ISPECL [rand(rator rwa); rand rwa; rand(rator lwa); rand lwa] PMUL_CONG_128)
                (CONJ in_eq mult_eq) in
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [wa_eq] (asl,w);;

(* OPTIMIZED STEPPING (2026-07-18): stores window 283-392 uses the Q18-latest
   per-step-discard stepper + midacc atomization instead of all-KEEPGH
   (proof 1573s -> ~470s cpu, peak heap ~2GB vs ~30GB).  Bridge expands midacc
   once, re-merges (KM tactic variants), folds H6..H2, WA-unify via BITBLAST.
   Same statement as before, only the tactic script changed. *)
(* WB_7/WB_8 midacc bridges leave a stray zero limb in each 64-bit lane
   (from the s392-carried mid entering the reduce as word 0 xor ...):
   collapse it before the bubble sort, then finish as LANE_FINISH_TAC. *)
let ZSUB0 = prove(`word_subword (word 0:int128) (0,64):64 word = word 0`, CONV_TAC WORD_BLAST);;
let ZSUB0b = prove(`word_subword (word 0:int128) (64,64):64 word = word 0`, CONV_TAC WORD_BLAST);;
let LANE_FINISH_Z_TAC : tactic =
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  CONV_TAC(RAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[SJ_COLLAPSE; SJ_COLLAPSE2] THEN REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[ZSUB0; ZSUB0b; WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  CONV_TAC(BINOP_CONV bubble_fix) THEN REFL_TAC;;

(* OPTIMIZED STEPPING (2026-07-18): stores window uses the Q18-latest
   per-step-discard stepper + midacc atomization instead of all-KEEPGH
   (same pattern as WB_7/WB_8; ~1.5-3x faster, flat memory).  *)


(* ============================================================================
   WB_4BLOCK: PROVED interactively (hyps=0, axioms=3).
   Tail map (entry s303 = pc+4220 = more_than_3, R3):
     304-309 KEEPGH; Q12 s309 = block-0 PT capture; s310 = store block-0
       (VSTEPS_FOLD + carry out_p) + KEEPGH discard.
     311-326 KEEPGH -> s326 pc+4312; Q12 s326 = block-1 (INC lanes);
       s327 = store block-1 (VSTEPS_FOLD + carry out_p, out_p+16) + discard.
     328-341 KEEPGH -> s341 pc+4372; Q12 s341 = block-2 (INC2 lanes);
       s342 = store block-2 (VSTEPS_FOLD + carry 3 readbacks) + discard.
     343-347 KEEPGH -> s347 pc+4396 (Q9=cph3 already); Q12 s347 = block-3
       (INC3 lanes) — capture BEFORE the shared reduce.
     348-369 KEEPGH -> s369 pc+4484; s370 = final store (PLAIN VSTEPS)
       + carry ALL FOUR out_p readbacks + KEEPGH discard + 4x DISCH.
     371-377 KEEPGH -> s377 pc+4516 = BRIDGE.
     BRIDGE (GMULT4): gmult4_dec = SPECL [a0.h4; brev cph1.h3; brev cph2.h2;
       brev cph3.h] GMULT4_FULL_CORRECT_BA; spec fold via spec_to_byteform_wb4
       (h2,h3,h4 conjuncts, ALL LEFT-NESTED so plain ASM_REWRITE, no DOT_SYM);
       then rewrites + karatsuba_mid + ABBREV_INNER_PMULS + MERGE_2BLK
       (12 qq atoms remain incl 2 unmerged mids keyed H3,H2) THEN
       FOLD_MID_HPOW "H3" THEN FOLD_MID_HPOW "H2" THEN WA_UNIFY THEN WV_UNIFY
       THEN ABBREV_WAWV THEN QQ0SPLIT/JOIN_EQ_SPLIT THEN CONJ_TAC THEN
       LANE_FINISH_TAC.  (QQ8_FOLD not needed at N=4 — its job is subsumed by
       FOLD_MID_HPOW "H2"?  NO: at N=3 the one leftover mid was H2-keyed and
       QQ8_FOLD_TAC grabbed it; at N=4 there are two (H3,H2) so use
       FOLD_MID_HPOW for both.  GENERAL RULE for band N: after MERGE,
       FOLD_MID_HPOW "H<N-1>" .. "H2" (rev order), then WA/WV unify.)
     378-379 ext/rev64 + Q19 s379 = brev gval; 380 tag store; final as before.

   GENERAL WB BAND STRUCTURE (N=2..8) — states shift by band:
     entry sE:      N=2:313/pc4348  N=3:309/4288  N=4:303/4220  N=5:297/4164?
                    N=6:290/4104?   N=7:282/4048?  N=8:270/4000?
     (cascade sEnd from ARM_STEPS_RESOLVE (278--sEnd); discover live per band)
     per full round k=0..N-2: ~6-16 steps; block-k PT capture right before its
       str; final block N-1 capture at the eor3 right after last cascade ldr.
     final store at pc+4484 (str q12,[x2] No_Offset) = PLAIN VSTEPS.
     bridge at pc+4516; ext/rev64; tag store pc+4524; exit pc+4528.
   ============================================================================ *)

let GCM_CTR_INC3_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))`,
        subst [`word 3:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;
let PACK4_ID, GMULT4_FULL_CORRECT_BA = build_GMULTn_fast 4;;
let spec_to_byteform_wb4 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2; word_bytereverse cph3] =
       polyval_reduce_prop3
        (word_xor
         (word_xor
          (word_xor
           (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h4))
           (word_pmul (word_bytereverse cph1) (byteswap128 h3)))
          (word_pmul (word_bytereverse cph2) (byteswap128 h2)))
         (word_pmul (word_bytereverse cph3) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`;
            `word_bytereverse cph2:int128`; `word_bytereverse cph3:int128`] GHASH_POLYVAL_ACC_4)] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* ============================================================================
   WB_5BLOCK PLAN (derived from disassembly, 2026-07-16).

   DISASSEMBLY FINDING: the cascade b.gt targets confirm the band entries:
   N=5 takes the #64 branch (b.gt at pc+3920, offset 244) -> entry pc+4164 =
   R4 region head (rev64 v8,v9 for the block-0 GHASH round vs h5=Q20).
   R4 = pc+4164..4216, exactly 14 instructions:
     rev64; eor v8,v16; ins v27; ldr q9(cph1); movi d16; pmull(q20);
     pmull2(q20); eor v27,v8; eor v17,v28; pmull v27(q21-mid); eor v19,v26;
     str q12 (BLOCK-0 STORE, 12th instr); eor v18,v27; eor3 v12,v9,v4,v29
     (BLOCK-1 PT, 14th instr; ks1 lives in Q4 = Q(8-N+1) for N=5).
   Then N=5 falls into the SHARED WB_4 tail at pc+4220: every WB_4 tail step
   s(304+k) = WB_5 step s(312+k), block indices shifted +1 (INC^k lanes).

   WB_5 TAIL MAP (entry s297 = pc+4164; Q12 = block-0 PT from the cascade
   preamble eor3 v12,v9,v0,v29 at pc+3804):
     298-308 KEEPGH (R4 round); Q12 s308 = block-0 capture (plain
       reconstruct+WORD_RULE — Q12 untouched since preamble); s309 = str
       q12,[x2],#16 block-0 store (VSTEPS_FOLD + carry out_p) + discard.
     310-317 KEEPGH (s311 = eor3 block-1 vs Q4); Q12 s317 = block-1 (INC
       lanes); s318 = store block-1 (VSTEPS_FOLD + carry out_p, out_p+16).
     319-334 KEEPGH (s319 = eor3 block-2 vs Q5); Q12 s334 = block-2 (INC2);
       s335 = store (VSTEPS_FOLD + carry 3 readbacks).
     336-349 KEEPGH (s...= eor3 block-3 vs Q6); Q12 s349 = block-3 (INC3);
       s350 = store (VSTEPS_FOLD + carry 4 readbacks).
     351-355 KEEPGH (eor3 block-4 vs Q7); Q12 s355 = block-4 (INC4 lanes) —
       capture BEFORE the shared reduce.
     356-377 KEEPGH -> s377 pc+4484; s378 = final store (PLAIN VSTEPS) +
       carry ALL FIVE out_p readbacks + KEEPGH discard + 5x DISCH.
     379-385 KEEPGH -> s385 pc+4516 = BRIDGE (GMULT5: spec_to_byteform_wb5
       + GSYM gmult5_dec pairs (a0,h5)(cph1,h4)(cph2,h3)(cph3,h2)(cph4,h);
       FOLD_MID_HPOW "H4" "H3" "H2").
     386-387 ext/rev64 + Q19 s387 = brev gval; 388 tag store; exit pc+4528.
   Front discards keep Q0..Q4: per-step 6..30 [5;6;7], bulk [5;6;7;30],
   after 256-265 [5;6;30].  Cascade (266--277) + (278--297).
   ============================================================================ *)

let GCM_CTR_INC4_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)))`,
        subst [`word 4:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;
let PACK5_ID, GMULT5_FULL_CORRECT_BA = build_GMULTn_fast 5;;
let spec_to_byteform_wb5 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h5 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
         word_bytereverse cph3; word_bytereverse cph4] =
       polyval_reduce_prop3
        (word_xor
         (word_xor
          (word_xor
           (word_xor
            (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h5))
            (word_pmul (word_bytereverse cph1) (byteswap128 h4)))
           (word_pmul (word_bytereverse cph2) (byteswap128 h3)))
          (word_pmul (word_bytereverse cph3) (byteswap128 h2)))
         (word_pmul (word_bytereverse cph4) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`;
            `word_bytereverse cph2:int128`; `word_bytereverse cph3:int128`;
            `word_bytereverse cph4:int128`] GHASH_POLYVAL_ACC_5)] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;
(* ------------------------------------------------------------------------- *)
(* AESV8_GCM_8X_DEC_256_WB_4BLOCK: whole-blocks dec variant, bit_len=512.     *)
(* Script assembled from the interactively-validated tail map above.          *)
(* ------------------------------------------------------------------------- *)
(* OPTIMIZED STEPPING (2026-07-18): stores window uses the Q18-latest
   per-step-discard stepper + midacc atomization instead of all-KEEPGH
   (same pattern as WB_7/WB_8; ~1.5-3x faster, flat memory).  *)


(* ------------------------------------------------------------------------- *)
(* AESV8_GCM_8X_DEC_256_WB_5BLOCK: whole-blocks dec variant, bit_len=640.     *)
(* PROVED INTERACTIVELY 2026-07-16 first-pass, no backtracking: the derived   *)
(* tail map (entry s297=pc+4164, captures s308/s317/s334/s349/s355, final     *)
(* store s378, bridge s385) was exactly right.                                *)
(* ------------------------------------------------------------------------- *)
(* OPTIMIZED STEPPING (2026-07-18): stores window uses the Q18-latest
   per-step-discard stepper + midacc atomization instead of all-KEEPGH
   (same pattern as WB_7/WB_8; ~1.5-3x faster, flat memory).  *)



(* ============================================================================
   WB_6BLOCK machinery.  GHASH_POLYVAL_ACC_6 does not exist in
   common/ghash_nblock_karatsuba.ml (only 2..5) — proved here from
   GHASH_POLYVAL_ACC_BATCHED with the same recipe; promote to common/ later.
   ============================================================================ *)
let GHASH_POLYVAL_ACC_6 = prove
 (`!(h:int128) (a:int128) (p:int128) (q:int128) (r:int128) (s:int128) (t:int128) (u:int128).
    ghash_polyval_acc h a [p:int128; q; r; s; t; u] =
    polyval_reduce_prop3
      (word_xor
        (word_pmul (word_xor a p) (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h) : 256 word)
       (word_xor
        (word_pmul q (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) : 256 word)
       (word_xor
        (word_pmul r (polyval_dot (polyval_dot (polyval_dot h h) h) h) : 256 word)
       (word_xor
        (word_pmul s (polyval_dot (polyval_dot h h) h) : 256 word)
       (word_xor
        (word_pmul t (polyval_dot h h) : 256 word)
        (word_pmul u h : 256 word))))))`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`h:int128`; `[q:int128; r; s; t; u]`; `a:int128`; `p:int128`]
                GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide; h_power; ARITH; SUB_0] THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[num_CONV `5`; num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`; h_power]);;
let GCM_CTR_INC5_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))))`,
        subst [`word 5:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;
let PACK6_ID, GMULT6_FULL_CORRECT_BA = build_GMULTn_fast 6;;
let spec_to_byteform_wb6 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h5 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h6 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
         word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5] =
       polyval_reduce_prop3
        (word_xor
         (word_xor
          (word_xor
           (word_xor
            (word_xor
             (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h6))
             (word_pmul (word_bytereverse cph1) (byteswap128 h5)))
            (word_pmul (word_bytereverse cph2) (byteswap128 h4)))
           (word_pmul (word_bytereverse cph3) (byteswap128 h3)))
          (word_pmul (word_bytereverse cph4) (byteswap128 h2)))
         (word_pmul (word_bytereverse cph5) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`;
            `word_bytereverse cph2:int128`; `word_bytereverse cph3:int128`;
            `word_bytereverse cph4:int128`; `word_bytereverse cph5:int128`] GHASH_POLYVAL_ACC_6)] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* AESV8_GCM_8X_DEC_256_WB_6BLOCK: whole-blocks dec variant, bit_len=768.     *)
(* PROVED INTERACTIVELY 2026-07-16 first-pass.  Tail map: entry s290=pc+4104  *)
(* (R5 head, N=6 takes the #80 branch; cascade RESOLVE (278--290));           *)
(* R5 = 291-296 + capture s296 (block-0 vs h6, plain reconstruct) + store     *)
(* s297; R4 = 298-316 + capture s316 (INC lanes) + store s317; then the       *)
(* shared WB_5 tail shifted +8: captures s325/s342/s357 (INC2/INC3/INC4),     *)
(* stores s326/s343/s358; final eor3 in 359-363, capture s363 (INC5 lanes);   *)
(* reduce 364-385; final store s386 (PLAIN VSTEPS + 6 readback carries);      *)
(* 387-393 KEEPGH -> bridge s393 pc+4516 (GMULT6, FOLD_MID_HPOW H5..H2);      *)
(* ext/rev64 394-395; tag store 396; exit pc+4528.                            *)
(* ------------------------------------------------------------------------- *)
(* OPTIMIZED STEPPING (2026-07-18): stores window uses the Q18-latest
   per-step-discard stepper + midacc atomization instead of all-KEEPGH
   (same pattern as WB_7/WB_8; ~1.5-3x faster, flat memory).  *)


(* ============================================================================
   WB_7BLOCK machinery (ACC_7 proved from BATCHED like ACC_6 below).
   ============================================================================ *)
let GHASH_POLYVAL_ACC_7 = prove
 (`!(h:int128) (a:int128) (p:int128) (q:int128) (r:int128) (s:int128) (t:int128) (u:int128) (v:int128).
    ghash_polyval_acc h a [p:int128; q; r; s; t; u; v] =
    polyval_reduce_prop3
      (word_xor
        (word_pmul (word_xor a p) (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h) h) : 256 word)
       (word_xor
        (word_pmul q (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h) : 256 word)
       (word_xor
        (word_pmul r (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) : 256 word)
       (word_xor
        (word_pmul s (polyval_dot (polyval_dot (polyval_dot h h) h) h) : 256 word)
       (word_xor
        (word_pmul t (polyval_dot (polyval_dot h h) h) : 256 word)
       (word_xor
        (word_pmul u (polyval_dot h h) : 256 word)
        (word_pmul v h : 256 word)))))))`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`h:int128`; `[q:int128; r; s; t; u; v]`; `a:int128`; `p:int128`]
                GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide; h_power; ARITH; SUB_0] THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[num_CONV `6`; num_CONV `5`; num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`; h_power]);;
let GCM_CTR_INC6_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)))))`,
        subst [`word 6:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;
let PACK7_ID, GMULT7_FULL_CORRECT_BA = build_GMULTn_fast 7;;
let spec_to_byteform_wb7 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h5 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h6 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h7 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
         word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5;
         word_bytereverse cph6] =
       polyval_reduce_prop3
        (word_xor
         (word_xor
          (word_xor
           (word_xor
            (word_xor
             (word_xor
              (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h7))
              (word_pmul (word_bytereverse cph1) (byteswap128 h6)))
             (word_pmul (word_bytereverse cph2) (byteswap128 h5)))
            (word_pmul (word_bytereverse cph3) (byteswap128 h4)))
           (word_pmul (word_bytereverse cph4) (byteswap128 h3)))
          (word_pmul (word_bytereverse cph5) (byteswap128 h2)))
         (word_pmul (word_bytereverse cph6) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`;
            `word_bytereverse cph2:int128`; `word_bytereverse cph3:int128`;
            `word_bytereverse cph4:int128`; `word_bytereverse cph5:int128`;
            `word_bytereverse cph6:int128`] GHASH_POLYVAL_ACC_7)] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* AESV8_GCM_8X_DEC_256_WB_7BLOCK: whole-blocks dec variant, bit_len=896.     *)
(* PROVED INTERACTIVELY 2026-07-16 first-pass.  Tail map: entry s282=pc+4048  *)
(* (R6 head; cascade RESOLVE (278--282)); R6 = 283-287 + capture s287         *)
(* (block-0 vs h7, plain reconstruct — NOTE only 5 KEEPGH steps then capture, *)
(* the eor3 for block-1 comes at pc+4028 BEFORE the R6 head so Q12 is         *)
(* block-0 all through) + store s288; R5 = 289-302 + capture s302 (INC) +     *)
(* store s303; then WB_6's map +6: captures s322/s331/s348/s363/s369          *)
(* (INC2..INC6), stores s323/332/349/364, final store s392 (PLAIN VSTEPS +    *)
(* 7 readback carries); 393-399 KEEPGH -> bridge s399 pc+4516 (GMULT7,        *)
(* FOLD_MID_HPOW H6..H2); ext/rev64 400-401; tag store 402; exit pc+4528.     *)
(* ------------------------------------------------------------------------- *)

(* ============================================================================
   WB_8BLOCK machinery + proof.

   N=8 SPECIFIC FINDINGS (2026-07-16):
   1. Cascade: X5=128 fails ALL the b.gt tests and falls through to pc+4000 =
      `b +420` -> the R7 head at pc+4004.  Cascade = RESOLVE (266--270) only
      (no mov-chain: all 8 keystreams already in Q0..Q7); s270 = pc+4000.
   2. R7 head: only TWO KEEPGH steps (271-272) then block-0 capture at s272 —
      the eor3 for block-1 sits at pc+4028 (later); Q12 is still the cascade
      preamble's block-0 eor3.  Store s273; R6 = 274-287 + capture s287 (INC)
      + store s288; then WB_7's tail map SHIFTED -14: captures
      s302/s322/s331/s348/s363/s369 (INC2..INC7), stores s303/323/332/349/364,
      final store s392 (PLAIN VSTEPS + 8 carries), bridge s399 = pc+4516,
      ext/rev64 400-401, tag store 402, exit pc+4528.
   3. MERGE BLOCKER: at N=8 the stock MERGE_2BLK_TAC (core.ml) mis-pairs the
      qq atoms — its find_pair takes the FIRST signature-compatible candidate
      and at N=8 that greedy choice pairs machine-lo with spec-hi atoms
      leaving 4 unmergeable leftovers; the WORD_RULE r1/u staging then fails.
      FIX = MERGE_ONE_ANY_TAC below: same pairing signature but tries ALL
      candidate pairs via FIRST (backtracking on the WORD_BLAST operand
      close), so a bad greedy pick self-corrects.  After MERGE_ANY_TAC two
      k13-garbage mids remain (qq37 vs qq28 keyed H7, qq42 vs qq41 keyed H8 —
      the le8block "k13-kill" pattern): close each with an explicit
      SUBGOAL merge using WB_MID_FIX + WORD_BLAST.  NO FOLD_MID_HPOW needed.
   ============================================================================ *)
let GHASH_POLYVAL_ACC_8 = prove
 (`!(h:int128) (a:int128) (p:int128) (q:int128) (r:int128) (s:int128) (t:int128) (u:int128) (v:int128) (w:int128).
    ghash_polyval_acc h a [p:int128; q; r; s; t; u; v; w] =
    polyval_reduce_prop3
      (word_xor
        (word_pmul (word_xor a p) (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h) h) h) : 256 word)
       (word_xor
        (word_pmul q (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h) h) : 256 word)
       (word_xor
        (word_pmul r (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h) : 256 word)
       (word_xor
        (word_pmul s (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) : 256 word)
       (word_xor
        (word_pmul t (polyval_dot (polyval_dot (polyval_dot h h) h) h) : 256 word)
       (word_xor
        (word_pmul u (polyval_dot (polyval_dot h h) h) : 256 word)
       (word_xor
        (word_pmul v (polyval_dot h h) : 256 word)
        (word_pmul w h : 256 word))))))))`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`h:int128`; `[q:int128; r; s; t; u; v; w]`; `a:int128`; `p:int128`]
                GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide; h_power; ARITH; SUB_0] THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[num_CONV `7`; num_CONV `6`; num_CONV `5`; num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`; h_power]);;
let GCM_CTR_INC7_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))))))`,
        subst [`word 7:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;
let PACK8_ID, GMULT8_FULL_CORRECT_BA = build_GMULTn_fast 8;;
let spec_to_byteform_wb8 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h5 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h6 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h7 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h8 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
         word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5;
         word_bytereverse cph6; word_bytereverse cph7] =
       polyval_reduce_prop3
        (word_xor
         (word_xor
          (word_xor
           (word_xor
            (word_xor
             (word_xor
              (word_xor
               (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h8))
               (word_pmul (word_bytereverse cph1) (byteswap128 h7)))
              (word_pmul (word_bytereverse cph2) (byteswap128 h6)))
             (word_pmul (word_bytereverse cph3) (byteswap128 h5)))
            (word_pmul (word_bytereverse cph4) (byteswap128 h4)))
           (word_pmul (word_bytereverse cph5) (byteswap128 h3)))
          (word_pmul (word_bytereverse cph6) (byteswap128 h2)))
         (word_pmul (word_bytereverse cph7) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`;
            `word_bytereverse cph2:int128`; `word_bytereverse cph3:int128`;
            `word_bytereverse cph4:int128`; `word_bytereverse cph5:int128`;
            `word_bytereverse cph6:int128`; `word_bytereverse cph7:int128`] GHASH_POLYVAL_ACC_8)] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* AESV8_GCM_8X_DEC_256_WB_8BLOCK: whole-blocks dec variant, bit_len=1024.    *)
(* PROVED INTERACTIVELY 2026-07-16 (one bridge retry: stock MERGE_2BLK        *)
(* mis-pairs at N=8 — see the machinery header note; fix = MERGE_ANY_TAC +    *)
(* two explicit k13-mid merges qq37/qq28 (H7) and qq42/qq41 (H8)).            *)
(* ------------------------------------------------------------------------- *)




(* OPTIMIZED STEPPING (2026-07-18): same Q18-latest/midacc pattern as WB_7
   (proof was the OOM-killer at ~26min/30GB; now ~600s cpu/~2GB).  The three
   midacc-side mids merge as qq14'/qq28 (H7), qq15'/qq34 (H1), qq16'/qq39 (H8). *)




(* ------------------------------------------------------------------------- *)
(*    Per-band tail tactics (cascade + GHASH + bridge + stores from s265)    *)
(* ------------------------------------------------------------------------- *)


let WB_TAIL_1_TAC =
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (266--277) THEN
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (278--313) THEN
  (* === tail 314..333 (GHASH multiply; KEEPGH keeps Q16-Q19 alive) === *)
  ARM_STEPS_FOLD_KEEPGH_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (314--333) THEN
  (* plaintext capture: the whole aese/aesmc tower XOR = aes256_encrypt (JRH) *)
  SUBGOAL_THEN `read Q12 (s333:armstate) = word_xor cph (aes256_encrypt (ctr0:int128)
      [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q12 s333`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q12 s333` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE;
   ALL_TAC] THEN
  (* 334 = str q12,[x2] (output store); carry the readback across the discard *)
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC [334] THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 out_p) s334` with _ -> false)
    then MP_TAC th else NO_TAC) THEN
  DISCARD_OLDSTATE_TAC "s334" THEN DISCH_TAC THEN
  (* 335..341 GHASH reduce; KEEPGH keeps Q16-Q19 threaded (Q19 s341 closes to
     an ~8.2k term over word_bytereverse xi / cph / h, NO state refs). *)
  ARM_STEPS_FOLD_KEEPGH_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (335--341) THEN
  (* === GHASH bridge at s341 (pc+4516, post eor v19,v19,v18) === *)
  SUBGOAL_THEN
    `read Q19 (s341:armstate) =
     polyval_dot (word_xor (word_bytereverse xi) (word_bytereverse cph))
       (byteswap128 h)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s341`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s341` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   GEN_REWRITE_TAC RAND_CONV
     [GSYM(REWRITE_RULE[LET_DEF; LET_END_DEF]
        (ISPECL [`word_xor (word_bytereverse xi) (word_bytereverse cph) : int128`;
          `byteswap128 h:int128`] GMULT_FULL_CORRECT_BA))] THEN
   REWRITE_TAC[byteswap128] THEN
   REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
   REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_PMUL_ATOMS_TAC THEN
   TRY(SUBGOAL_THEN `qq5:int128 = qq2` (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "qq5" THEN EXPAND_TAC "qq2" THEN REWRITE_TAC[karatsuba_mid] THEN
     ((MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST)
      ORELSE (GEN_REWRITE_TAC LAND_CONV [WORD_PMUL_SYM] THEN
              MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST));
     ALL_TAC]) THEN
   REWRITE_TAC[SUBWORD0_LEMMAS; WORD_XOR_0] THEN REWRITE_TAC[WORD_XOR_0] THEN
   REWRITE_TAC[PMUL_W_64_128] THEN
   REWRITE_TAC[JOINMID] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   ABBREV_TAC `xll:64 word = word_subword (qq0:int128) (0,64)` THEN
   ABBREV_TAC `xlh:64 word = word_subword (qq0:int128) (64,64)` THEN
   ABBREV_TAC `xhl:64 word = word_subword (qq1:int128) (0,64)` THEN
   ABBREV_TAC `xhh:64 word = word_subword (qq1:int128) (64,64)` THEN
   ABBREV_TAC `xml:64 word = word_subword (qq2:int128) (0,64)` THEN
   ABBREV_TAC `xmh:64 word = word_subword (qq2:int128) (64,64)` THEN
   ABBREV_TAC
    `r1:(128)word = word_xor (word_xor (word_shl (word_zx (xhl:(64)word):(128)word) 63)
                                       (word_shl (word_zx xhl:(128)word) 62))
                             (word_shl (word_zx xhl:(128)word) 57)` THEN
   SUBGOAL_THEN
    `word_xor (word_xor (word_subword (word_shl (word_zx (xhl:(64)word):(128)word) 63) (0,64):(64)word)
                        (word_subword (word_shl (word_zx xhl:(128)word) 62) (0,64):(64)word))
              (word_subword (word_shl (word_zx xhl:(128)word) 57) (0,64):(64)word) =
     word_subword (r1:(128)word) (0,64):(64)word`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
   SUBGOAL_THEN
    `word_xor (word_xor (word_subword (word_shl (word_zx (xhl:(64)word):(128)word) 63) (64,64):(64)word)
                        (word_subword (word_shl (word_zx xhl:(128)word) 62) (64,64):(64)word))
              (word_subword (word_shl (word_zx xhl:(128)word) 57) (64,64):(64)word) =
     word_subword (r1:(128)word) (64,64):(64)word`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
   ABBREV_TAC `u:(64)word = word_xor (word_xor (word_subword (r1:128 word) (0,64)) (xhh:64 word)) (word_xor (word_xor (xll:64 word) (xhl:64 word)) (xml:64 word))` THEN
   SUBGOAL_THEN
    `word_xor (word_xor (xhh:64 word) (word_xor (word_xor (xml:64 word) (xhl:64 word)) (xll:64 word))) (word_subword (r1:128 word) (0,64)) = u`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "u" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
   ABBREV_TAC
    `r2:(128)word = word_xor (word_xor (word_shl (word_zx (u:(64)word):(128)word) 63)
                                       (word_shl (word_zx u:(128)word) 62))
                             (word_shl (word_zx u:(128)word) 57)` THEN
   SUBGOAL_THEN
    `word_xor (word_xor (word_subword (word_shl (word_zx (u:(64)word):(128)word) 63) (0,64):(64)word)
                        (word_subword (word_shl (word_zx u:(128)word) 62) (0,64):(64)word))
              (word_subword (word_shl (word_zx u:(128)word) 57) (0,64):(64)word) =
     word_subword (r2:(128)word) (0,64):(64)word`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r2" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
   SUBGOAL_THEN
    `word_xor (word_xor (word_subword (word_shl (word_zx (u:(64)word):(128)word) 63) (64,64):(64)word)
                        (word_subword (word_shl (word_zx u:(128)word) 62) (64,64):(64)word))
              (word_subword (word_shl (word_zx u:(128)word) 57) (64,64):(64)word) =
     word_subword (r2:(128)word) (64,64):(64)word`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r2" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
   TRY(SUBGOAL_THEN `qq0:int128 = word_join (xlh:64 word) (xll:64 word)`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "xll" THEN EXPAND_TAC "xlh" THEN CONV_TAC WORD_BLAST; ALL_TAC]) THEN
   CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = polyval_dot (word_xor (word_bytereverse xi)
    (word_bytereverse cph)) (byteswap128 h)` THEN
  (* 342 ext (half-swap), 343 rev64 -> Q19 = word_bytereverse gval *)
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (342--343) THEN
  SUBGOAL_THEN `read Q19 (s343:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s343`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s343` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  (* 344 = str q19,[x3] (tag store); exit at pc+4528 *)
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC [344] THEN
  DISCARD_COUNTER_ONLY_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
  [EXPAND_TAC "gval" THEN AP_TERM_TAC THEN REWRITE_TAC[GHASH_1BLOCK_CORRECT];
   REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
   REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[]];;


let WB_TAIL_2_TAC =
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (266--277) THEN
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (278--313) THEN
  (* === more_than_1 block-0 GHASH round; capture block-0 PT at s319 === *)
  ARM_STEPS_FOLD_KEEPGH_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (314--319) THEN
  SUBGOAL_THEN `read Q12 (s319:armstate) = word_xor cph0 (aes256_encrypt (ctr0:int128)
      [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q12 s319`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q12 s319` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE;
   ALL_TAC] THEN
  (* s320 = st1 v12,[x2],#16 (block-0 PT store); carry readback across discard *)
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC [320] THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 out_p) s320` with _ -> false)
    then MP_TAC th else NO_TAC) THEN
  DISCARD_OLDSTATE_KEEPGH_TAC "s320" THEN DISCH_TAC THEN
  (* 321-325: block-1 PT lands in Q12 via eor3 v12,v9,v7,v29; capture with
     GCM_CTR_INC_LANES folding the keystream input to gcm_ctr_inc ctr0 *)
  ARM_STEPS_FOLD_KEEPGH_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (321--325) THEN
  SUBGOAL_THEN `read Q12 (s325:armstate) = word_xor cph1 (aes256_encrypt
      (gcm_ctr_inc ctr0:int128)
      [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q12 s325`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q12 s325` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE;
   ALL_TAC] THEN
  (* 326-347: block-1 GHASH round + start of shared reduction *)
  ARM_STEPS_FOLD_KEEPGH_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (326--347) THEN
  (* s348 = str q12,[x2] (block-1 PT store).  Plain VSTEPS (the FOLD variant's
     simplifier chokes here); carry BOTH out_p readbacks across the discard. *)
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC [348] THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 (word_add out_p (word 16))) s348` with _ -> false)
    then MP_TAC th else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 out_p) s348` with _ -> false)
    then MP_TAC th else NO_TAC) THEN
  DISCARD_OLDSTATE_KEEPGH_TAC "s348" THEN DISCH_TAC THEN DISCH_TAC THEN
  (* 349-355: single Prop3 reduction folding both blocks -> bridge at s355 *)
  ARM_STEPS_FOLD_KEEPGH_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (349--355) THEN
  (* === GMULT2 bridge at s355 (pc+4516, post eor v19,v19,v18) === *)
  SUBGOAL_THEN
    `read Q19 (s355:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s355`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s355` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   WB2_GMULT2_BRIDGE_TAC;
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      [word_bytereverse cph0; word_bytereverse cph1]` THEN
  (* 356 ext (half-swap), 357 rev64 -> Q19 = word_bytereverse gval *)
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (356--357) THEN
  SUBGOAL_THEN `read Q19 (s357:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s357`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s357` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  (* 358 = str q19,[x3] (tag store); exit at pc+4528 *)
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC [358] THEN
  DISCARD_COUNTER_ONLY_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[];;


let WB_TAIL_3_TAC =
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (266--277) THEN
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (278--309)  THEN
  ARM_STEPS_FOLD_Q18LATEST_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (310--359) THEN
  ABBREV_TAC `midacc:int128 = read Q18 s359` THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `midacc:int128` with _ -> false)
    then ASSUME_TAC (SYM th) else NO_TAC) THEN
  ARM_STEPS_FOLD_KEEPGH_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (360--366) THEN
  SUBGOAL_THEN
    `read Q19 (s366:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s366`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s366` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   (fun (asl,w) ->
     let gmult3_dec = REWRITE_RULE[LET_DEF;LET_END_DEF]
       (SPECL [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h3:int128`;
               `word_bytereverse cph1:int128`; `byteswap128 h2:int128`;
               `word_bytereverse cph2:int128`; `byteswap128 h:int128`] GMULT3_FULL_CORRECT_BA) in
     let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
     let h3asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h3` with _->false) asl) in
     (GEN_REWRITE_TAC RAND_CONV
        [TRANS (MP spec_to_byteform_wb3 (CONJ h2asm h3asm)) (GSYM gmult3_dec)]) (asl,w)) THEN
   REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
   REWRITE_TAC[byteswap128] THEN REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
   REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
   REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   REWRITE_TAC[karatsuba_mid] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN MERGE_ANY_TAC THEN
   (fun (asl,w) ->
     let (_,th) = List.find (fun (_,th) ->
       try rand(concl th) = `midacc:int128` && is_eq(concl th) with _ -> false) asl in
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SYM th] (asl,w)) THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN MERGE_ANY_TAC THEN
   MERGE_QQPAIR_KM_TAC "qq4'" "qq9" THEN
   MERGE_QQPAIR_KM_TAC "qq5'" "qq14" THEN
   MAP_EVERY FOLD_MID_HPOW_KM ["H2"] THEN
   WA_UNIFY_BB_TAC THEN ABBREV_WAWV_TAC THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN LANE_FINISH_Z_TAC;
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2]` THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (367--368) THEN
  SUBGOAL_THEN `read Q19 (s368:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s368`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s368` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC [369] THEN
  DISCARD_COUNTER_ONLY_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(FIRST(map (fun lanes ->
        GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [lanes] THEN
        REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC)
      [GCM_CTR_INC_LANES; GCM_CTR_INC2_LANES]) THEN NO_TAC) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[];;


let WB_TAIL_4_TAC =
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (266--277) THEN
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (278--303)  THEN
  ARM_STEPS_FOLD_Q18LATEST_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (304--370) THEN
  ABBREV_TAC `midacc:int128 = read Q18 s370` THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `midacc:int128` with _ -> false)
    then ASSUME_TAC (SYM th) else NO_TAC) THEN
  ARM_STEPS_FOLD_KEEPGH_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (371--377) THEN
  SUBGOAL_THEN
    `read Q19 (s377:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1;
        word_bytereverse cph2; word_bytereverse cph3]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s377`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s377` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   (fun (asl,w) ->
     let gmult4_dec = REWRITE_RULE[LET_DEF;LET_END_DEF]
       (SPECL [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h4:int128`;
               `word_bytereverse cph1:int128`; `byteswap128 h3:int128`;
               `word_bytereverse cph2:int128`; `byteswap128 h2:int128`;
               `word_bytereverse cph3:int128`; `byteswap128 h:int128`] GMULT4_FULL_CORRECT_BA) in
     let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
     let h3asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h3` with _->false) asl) in
     let h4asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h4` with _->false) asl) in
     (GEN_REWRITE_TAC RAND_CONV
        [TRANS (MP spec_to_byteform_wb4 (CONJ h2asm (CONJ h3asm h4asm))) (GSYM gmult4_dec)]) (asl,w)) THEN
   REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
   REWRITE_TAC[byteswap128] THEN REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
   REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
   REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   REWRITE_TAC[karatsuba_mid] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN MERGE_ANY_TAC THEN
   (fun (asl,w) ->
     let (_,th) = List.find (fun (_,th) ->
       try rand(concl th) = `midacc:int128` && is_eq(concl th) with _ -> false) asl in
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SYM th] (asl,w)) THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN MERGE_ANY_TAC THEN
   MERGE_QQPAIR_KM_TAC "qq6'" "qq14" THEN
   MERGE_QQPAIR_KM_TAC "qq7'" "qq19" THEN
   MAP_EVERY FOLD_MID_HPOW_KM ["H3";"H2"] THEN
   WA_UNIFY_BB_TAC THEN ABBREV_WAWV_TAC THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN LANE_FINISH_Z_TAC;
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
       word_bytereverse cph3]` THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (378--379) THEN
  SUBGOAL_THEN `read Q19 (s379:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s379`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s379` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC [380] THEN
  DISCARD_COUNTER_ONLY_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(FIRST(map (fun lanes ->
        GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [lanes] THEN
        REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC)
      [GCM_CTR_INC_LANES; GCM_CTR_INC2_LANES; GCM_CTR_INC3_LANES]) THEN NO_TAC) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[];;


let WB_TAIL_5_TAC =
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (266--277) THEN
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (278--297)  THEN
  ARM_STEPS_FOLD_Q18LATEST_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (298--378) THEN
  ABBREV_TAC `midacc:int128 = read Q18 s378` THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `midacc:int128` with _ -> false)
    then ASSUME_TAC (SYM th) else NO_TAC) THEN
  ARM_STEPS_FOLD_KEEPGH_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (379--385) THEN
  SUBGOAL_THEN
    `read Q19 (s385:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1;
        word_bytereverse cph2; word_bytereverse cph3; word_bytereverse cph4]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s385`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s385` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   (fun (asl,w) ->
     let gmult5_dec = REWRITE_RULE[LET_DEF;LET_END_DEF]
       (SPECL [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h5:int128`;
               `word_bytereverse cph1:int128`; `byteswap128 h4:int128`;
               `word_bytereverse cph2:int128`; `byteswap128 h3:int128`;
               `word_bytereverse cph3:int128`; `byteswap128 h2:int128`;
               `word_bytereverse cph4:int128`; `byteswap128 h:int128`] GMULT5_FULL_CORRECT_BA) in
     let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
     let h3asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h3` with _->false) asl) in
     let h4asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h4` with _->false) asl) in
     let h5asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h5` with _->false) asl) in
     (GEN_REWRITE_TAC RAND_CONV
        [TRANS (MP spec_to_byteform_wb5 (CONJ h2asm (CONJ h3asm (CONJ h4asm h5asm)))) (GSYM gmult5_dec)]) (asl,w)) THEN
   REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
   REWRITE_TAC[byteswap128] THEN REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
   REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
   REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   REWRITE_TAC[karatsuba_mid] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN MERGE_ANY_TAC THEN
   (fun (asl,w) ->
     let (_,th) = List.find (fun (_,th) ->
       try rand(concl th) = `midacc:int128` && is_eq(concl th) with _ -> false) asl in
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SYM th] (asl,w)) THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN MERGE_ANY_TAC THEN
   MERGE_QQPAIR_KM_TAC "qq8'" "qq19" THEN
   MERGE_QQPAIR_KM_TAC "qq9'" "qq24" THEN
   MAP_EVERY FOLD_MID_HPOW_KM ["H4";"H3";"H2"] THEN
   WA_UNIFY_BB_TAC THEN ABBREV_WAWV_TAC THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN LANE_FINISH_Z_TAC;
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
       word_bytereverse cph3; word_bytereverse cph4]` THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (386--387) THEN
  SUBGOAL_THEN `read Q19 (s387:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s387`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s387` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC [388] THEN
  DISCARD_COUNTER_ONLY_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(FIRST(map (fun lanes ->
        GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [lanes] THEN
        REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC)
      [GCM_CTR_INC_LANES; GCM_CTR_INC2_LANES; GCM_CTR_INC3_LANES; GCM_CTR_INC4_LANES]) THEN NO_TAC) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[];;


let WB_TAIL_6_TAC =
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (266--277) THEN
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (278--290)  THEN
  ARM_STEPS_FOLD_Q18LATEST_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (291--386) THEN
  ABBREV_TAC `midacc:int128 = read Q18 s386` THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `midacc:int128` with _ -> false)
    then ASSUME_TAC (SYM th) else NO_TAC) THEN
  ARM_STEPS_FOLD_KEEPGH_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (387--393) THEN
  SUBGOAL_THEN
    `read Q19 (s393:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
        word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s393`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s393` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   (fun (asl,w) ->
     let gmult6_dec = REWRITE_RULE[LET_DEF;LET_END_DEF]
       (SPECL [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h6:int128`;
               `word_bytereverse cph1:int128`; `byteswap128 h5:int128`;
               `word_bytereverse cph2:int128`; `byteswap128 h4:int128`;
               `word_bytereverse cph3:int128`; `byteswap128 h3:int128`;
               `word_bytereverse cph4:int128`; `byteswap128 h2:int128`;
               `word_bytereverse cph5:int128`; `byteswap128 h:int128`] GMULT6_FULL_CORRECT_BA) in
     let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
     let h3asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h3` with _->false) asl) in
     let h4asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h4` with _->false) asl) in
     let h5asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h5` with _->false) asl) in
     let h6asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h6` with _->false) asl) in
     (GEN_REWRITE_TAC RAND_CONV
        [TRANS (MP spec_to_byteform_wb6 (CONJ h2asm (CONJ h3asm (CONJ h4asm (CONJ h5asm h6asm))))) (GSYM gmult6_dec)]) (asl,w)) THEN
   REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
   REWRITE_TAC[byteswap128] THEN REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
   REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
   REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   REWRITE_TAC[karatsuba_mid] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN MERGE_ANY_TAC THEN
   (fun (asl,w) ->
     let (_,th) = List.find (fun (_,th) ->
       try rand(concl th) = `midacc:int128` && is_eq(concl th) with _ -> false) asl in
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SYM th] (asl,w)) THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN MERGE_ANY_TAC THEN
   MERGE_QQPAIR_KM_TAC "qq10'" "qq24" THEN
   MERGE_QQPAIR_KM_TAC "qq11'" "qq29" THEN
   MAP_EVERY FOLD_MID_HPOW_KM ["H5";"H4";"H3";"H2"] THEN
   WA_UNIFY_BB_TAC THEN ABBREV_WAWV_TAC THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN LANE_FINISH_Z_TAC;
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
       word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5]` THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (394--395) THEN
  SUBGOAL_THEN `read Q19 (s395:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s395`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s395` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC [396] THEN
  DISCARD_COUNTER_ONLY_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(FIRST(map (fun lanes ->
        GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [lanes] THEN
        REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC)
      [GCM_CTR_INC_LANES; GCM_CTR_INC2_LANES; GCM_CTR_INC3_LANES; GCM_CTR_INC4_LANES;
       GCM_CTR_INC5_LANES]) THEN NO_TAC) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[];;


let WB_TAIL_7_TAC =
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (266--277) THEN
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (278--282)  THEN
  ARM_STEPS_FOLD_Q18LATEST_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (283--392) THEN
  ABBREV_TAC `midacc:int128 = read Q18 s392` THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `midacc:int128` with _ -> false)
    then ASSUME_TAC (SYM th) else NO_TAC) THEN
  ARM_STEPS_FOLD_KEEPGH_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (393--399) THEN
  SUBGOAL_THEN
    `read Q19 (s399:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
        word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5;
        word_bytereverse cph6]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s399`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s399` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   (fun (asl,w) ->
     let gmult7_dec = REWRITE_RULE[LET_DEF;LET_END_DEF]
       (SPECL [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h7:int128`;
               `word_bytereverse cph1:int128`; `byteswap128 h6:int128`;
               `word_bytereverse cph2:int128`; `byteswap128 h5:int128`;
               `word_bytereverse cph3:int128`; `byteswap128 h4:int128`;
               `word_bytereverse cph4:int128`; `byteswap128 h3:int128`;
               `word_bytereverse cph5:int128`; `byteswap128 h2:int128`;
               `word_bytereverse cph6:int128`; `byteswap128 h:int128`] GMULT7_FULL_CORRECT_BA) in
     let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
     let h3asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h3` with _->false) asl) in
     let h4asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h4` with _->false) asl) in
     let h5asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h5` with _->false) asl) in
     let h6asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h6` with _->false) asl) in
     let h7asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h7` with _->false) asl) in
     (GEN_REWRITE_TAC RAND_CONV
        [TRANS (MP spec_to_byteform_wb7 (CONJ h2asm (CONJ h3asm (CONJ h4asm (CONJ h5asm (CONJ h6asm h7asm)))))) (GSYM gmult7_dec)]) (asl,w)) THEN
   REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
   REWRITE_TAC[byteswap128] THEN REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
   REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
   REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   REWRITE_TAC[karatsuba_mid] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN MERGE_ANY_TAC THEN
   (fun (asl,w) ->
     let (_,th) = List.find (fun (_,th) ->
       try rand(concl th) = `midacc:int128` && is_eq(concl th) with _ -> false) asl in
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SYM th] (asl,w)) THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN MERGE_ANY_TAC THEN
   MERGE_QQPAIR_KM_TAC "qq12'" "qq29" THEN
   MERGE_QQPAIR_KM_TAC "qq13'" "qq34" THEN
   MAP_EVERY FOLD_MID_HPOW_KM ["H6";"H5";"H4";"H3";"H2"] THEN
   WA_UNIFY_BB_TAC THEN ABBREV_WAWV_TAC THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN LANE_FINISH_Z_TAC;
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
       word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5;
       word_bytereverse cph6]` THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (400--401) THEN
  SUBGOAL_THEN `read Q19 (s401:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s401`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s401` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC [402] THEN
  DISCARD_COUNTER_ONLY_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(FIRST(map (fun lanes ->
        GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [lanes] THEN
        REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC)
      [GCM_CTR_INC_LANES; GCM_CTR_INC2_LANES; GCM_CTR_INC3_LANES; GCM_CTR_INC4_LANES;
       GCM_CTR_INC5_LANES; GCM_CTR_INC6_LANES]) THEN NO_TAC) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[];;


let WB_TAIL_8_TAC =
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (266--270)  THEN
  (* stores window: Q18-latest per-step discard; readbacks self-propagate *)
  ARM_STEPS_FOLD_Q18LATEST_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (271--392) THEN
  ABBREV_TAC `midacc:int128 = read Q18 s392` THEN
  (* orient the defn tree=midacc so steppers substitute TOWARD the atom *)
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `midacc:int128` with _ -> false)
    then ASSUME_TAC (SYM th) else NO_TAC) THEN
  ARM_STEPS_FOLD_KEEPGH_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (393--399) THEN
  SUBGOAL_THEN
    `read Q19 (s399:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
        word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5;
        word_bytereverse cph6; word_bytereverse cph7]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s399`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s399` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
      (fun (asl,w) ->
     let gmult8_dec = REWRITE_RULE[LET_DEF;LET_END_DEF]
       (SPECL [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h8:int128`;
               `word_bytereverse cph1:int128`; `byteswap128 h7:int128`;
               `word_bytereverse cph2:int128`; `byteswap128 h6:int128`;
               `word_bytereverse cph3:int128`; `byteswap128 h5:int128`;
               `word_bytereverse cph4:int128`; `byteswap128 h4:int128`;
               `word_bytereverse cph5:int128`; `byteswap128 h3:int128`;
               `word_bytereverse cph6:int128`; `byteswap128 h2:int128`;
               `word_bytereverse cph7:int128`; `byteswap128 h:int128`] GMULT8_FULL_CORRECT_BA) in
     let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
     let h3asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h3` with _->false) asl) in
     let h4asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h4` with _->false) asl) in
     let h5asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h5` with _->false) asl) in
     let h6asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h6` with _->false) asl) in
     let h7asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h7` with _->false) asl) in
     let h8asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h8` with _->false) asl) in
     (GEN_REWRITE_TAC RAND_CONV
        [TRANS (MP spec_to_byteform_wb8 (CONJ h2asm (CONJ h3asm (CONJ h4asm (CONJ h5asm (CONJ h6asm (CONJ h7asm h8asm))))))) (GSYM gmult8_dec)]) (asl,w)) THEN
      REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
      REWRITE_TAC[byteswap128] THEN REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
      REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
      REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
      REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
      REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
      REWRITE_TAC[karatsuba_mid] THEN
      ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
      MERGE_ANY_TAC THEN
   (fun (asl,w) ->
     let (_,th) = List.find (fun (_,th) ->
       try rand(concl th) = `midacc:int128` && is_eq(concl th) with _ -> false) asl in
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SYM th] (asl,w)) THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN MERGE_ANY_TAC THEN
   MERGE_QQPAIR_KM_TAC "qq14'" "qq28" THEN
   MERGE_QQPAIR_KM_TAC "qq15'" "qq34" THEN
   MERGE_QQPAIR_KM_TAC "qq16'" "qq39" THEN
   MAP_EVERY FOLD_MID_HPOW_KM ["H6";"H5";"H4";"H3";"H2"] THEN
   WA_UNIFY_BB_TAC THEN ABBREV_WAWV_TAC THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN LANE_FINISH_TAC;
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
       word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5;
       word_bytereverse cph6; word_bytereverse cph7]` THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (400--401) THEN
  SUBGOAL_THEN `read Q19 (s401:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s401`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s401` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC [402] THEN
  DISCARD_COUNTER_ONLY_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(FIRST(map (fun lanes ->
        GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [lanes] THEN
        REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC)
      [GCM_CTR_INC_LANES; GCM_CTR_INC2_LANES; GCM_CTR_INC3_LANES; GCM_CTR_INC4_LANES;
       GCM_CTR_INC5_LANES; GCM_CTR_INC6_LANES; GCM_CTR_INC7_LANES]) THEN NO_TAC) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[];;



(* ------------------------------------------------------------------------- *)
(*         Shared front WB_FRONT_BUF + the 8 recomposed band theorems        *)
(* ------------------------------------------------------------------------- *)


(* ---- scalar N-folding lemmas (the two nblk-dependent scalar ops) ---------- *)
let USHR_128NBLK = prove
 (`!nblk. 1 <= nblk /\ nblk <= 8
        ==> word_ushr (word (128 * nblk):int64) 3 = word (16 * nblk)`,
  GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `1 <= n /\ n <= 8 <=>
    n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV);;

let AND_MASK_16NBLK = prove
 (`!nblk. 1 <= nblk /\ nblk <= 8
        ==> word_and (word_sub (word (16 * nblk)) (word 1))
                     (word 18446744073709551488):int64 = word 0`,
  GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `1 <= n /\ n <= 8 <=>
    n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV);;

(* ---- input-lane bridge (local re-proof of le3block's lemma; only needs
        READ_BYTES_AND_BYTE128_MERGE from aes_xts_common) -------------------- *)
let INPUT_BYTES_TO_BYTE128_LANES = prove
 (`!n (in_p:int64) (x:byte list) s.
    16 * n <= LENGTH x /\
    read (memory :> bytes (in_p, 16 * n)) s = num_of_bytelist (SUB_LIST (0, 16 * n) x)
    ==> !k. k < n ==> read (memory :> bytes128 (word_add in_p (word (16 * k)))) s =
                      bytes_to_int128 (SUB_LIST (16 * k, 16) x)`,
  INDUCT_TAC THENL [REWRITE_TAC[LT]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`in_p:int64`; `16 * n`; `x:byte list`; `s:armstate`] READ_BYTES_AND_BYTE128_MERGE) THEN
  ANTS_TAC THENL [REWRITE_TAC[ARITH_RULE `16 * n + 16 = 16 * SUC n`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL [REWRITE_TAC[ARITH_RULE `16 * n + 16 = 16 * SUC n`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[LT] THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`in_p:int64`; `x:byte list`; `s:armstate`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[]]);;

(* ---- shared front tactics ------------------------------------------------- *)
(* Buffer prep: SUB_LIST length collapse, block-0 lane, the two scalar facts. *)
let WB_FRONT_PREP_BUF_TAC =
  SUBGOAL_THEN `SUB_LIST (0, 16 * nblk) (ibytes:byte list) = ibytes` ASSUME_TAC THENL
   [MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes128 in_p) s0 = bytes_to_int128 (SUB_LIST (0,16) ibytes)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `s0:armstate`] INPUT_BYTES_TO_BYTE128_LANES) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN DISCH_THEN(MP_TAC o SPEC `0`) THEN
    ASM_SIMP_TAC[LE_1; MULT_CLAUSES; WORD_ADD_0]; ALL_TAC] THEN
  SUBGOAL_THEN `word_ushr (word (128 * nblk):int64) 3 = word (16 * nblk)` ASSUME_TAC THENL
   [MATCH_MP_TAC USHR_128NBLK THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `word_and (word_sub (word (16 * nblk)) (word 1)) (word 18446744073709551488):int64 = word 0` ASSUME_TAC THENL
   [MATCH_MP_TAC AND_MASK_16NBLK THEN ASM_REWRITE_TAC[]; ALL_TAC];;

(* Union front steps 1..265: keeps ALL Q0..Q7 towers (discard only Q30 piles).
   The single b.ge (step 260) is nblk-independent (X5 collapses to in_p by s173
   via AND_MASK_16NBLK, so cmp@240 is in_p vs in_p). *)
let WB_FRONT_STEP_TAC =
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (1--5) THEN
  EVERY(map (fun i -> ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (i--i) THEN
             GCM_SIMD_SIMPLIFY_TAC) (6--30)) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (31--84) THEN mk_discard2 [30] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (85--173) THEN mk_discard2 [30] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (174--177) THEN
  GCM_SIMD_SIMPLIFY_TAC THEN mk_discard2 [30] THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (178--189) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[Q19_BREVXI]) THEN mk_discard2 [30] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (190--254) THEN
  mk_discard2 [30] THEN GCM_SIMD_SIMPLIFY_TAC THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC [255] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_SUB_REFL; INT_OF_NUM_EQ]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (256--265) THEN
  GCM_SIMD_SIMPLIFY_TAC THEN mk_discard2 [30] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_sub (word_add in_p (word (16 * nblk))) in_p:int64 = word (16 * nblk)`]);;

(* ---- WB_FRONT_BUF construction (route A: harvest the s265 state) ----------
   The postcond has 8 raw 13-round aese/aesmc towers (~2666ch each) that cannot
   be hand-written, and the printed statement does NOT reparse (type annots
   lost).  So: run the front once against a MINIMAL postcond, harvest the s265
   assumptions into the real postcond term, assemble the goal, prove.  The
   front therefore simulates twice (once to harvest, once in the proof). ---- *)

let wb_front_pre_tm = `\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
          read PC s = word (pc + 0x20) /\ read SP s = stackpointer /\
          C_ARGUMENTS [in_p; word (128 * nblk); out_p; xi_p; ivec_p; key_p; htbl_p] s /\
          read (memory :> bytes (in_p, 16 * nblk)) s = num_of_bytelist ibytes /\
          read (memory :> bytes128 xi_p) s = xi /\
          read (memory :> bytes128 ivec_p) s = ctr0 /\
          read (memory :> bytes128 key_p) s = k0 /\
          read (memory :> bytes128 (word_add key_p (word 16))) s = k1 /\
          read (memory :> bytes128 (word_add key_p (word 32))) s = k2 /\
          read (memory :> bytes128 (word_add key_p (word 48))) s = k3 /\
          read (memory :> bytes128 (word_add key_p (word 64))) s = k4 /\
          read (memory :> bytes128 (word_add key_p (word 80))) s = k5 /\
          read (memory :> bytes128 (word_add key_p (word 96))) s = k6 /\
          read (memory :> bytes128 (word_add key_p (word 112))) s = k7 /\
          read (memory :> bytes128 (word_add key_p (word 128))) s = k8 /\
          read (memory :> bytes128 (word_add key_p (word 144))) s = k9 /\
          read (memory :> bytes128 (word_add key_p (word 160))) s = k10 /\
          read (memory :> bytes128 (word_add key_p (word 176))) s = k11 /\
          read (memory :> bytes128 (word_add key_p (word 192))) s = k12 /\
          read (memory :> bytes128 (word_add key_p (word 208))) s = k13 /\
          read (memory :> bytes128 (word_add key_p (word 224))) s = k14 /\
          htable_mem_dec h htbl_p s`;;

let wb_front_frame_tm = `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(out_p:int64, 16 * nblk); memory :> bytes(xi_p:int64, 16);
                 memory :> bytes(ivec_p:int64, 16); memory :> bytes(stackpointer:int64, 80)] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31]`;;

let wb_front_hyps_tm = `1 <= nblk /\ nblk <= 8 /\ LENGTH (ibytes:byte list) = 16 * nblk /\
    aligned 16 stackpointer /\
    nonoverlapping (word pc, 4560) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, 4560) (out_p:int64, 16 * nblk) /\
    nonoverlapping (word pc, 4560) (xi_p:int64, 16) /\
    nonoverlapping (word pc, 4560) (ivec_p:int64, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 16 * nblk) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 240) /\
    nonoverlapping (ivec_p, 16) (htbl_p:int64, 192) /\
    nonoverlapping (in_p, 16 * nblk) (stackpointer, 80) /\
    nonoverlapping (key_p, 240) (stackpointer, 80) /\
    nonoverlapping (htbl_p, 192) (stackpointer, 80) /\
    nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
    nonoverlapping (xi_p, 16) (in_p, 16 * nblk) /\
    nonoverlapping (xi_p, 16) (key_p, 240) /\
    nonoverlapping (xi_p, 16) (htbl_p, 192) /\
    nonoverlapping (xi_p, 16) (stackpointer, 80)`;;

let wb_front_vars = [`pc:num`;`stackpointer:int64`;`out_p:int64`;`xi_p:int64`;`ivec_p:int64`;
            `in_p:int64`;`key_p:int64`;`htbl_p:int64`;`nblk:num`;`ibytes:byte list`;
            `xi:int128`;`ctr0:int128`;`k0:int128`;`k1:int128`;`k2:int128`;`k3:int128`;
            `k4:int128`;`k5:int128`;`k6:int128`;`k7:int128`;`k8:int128`;`k9:int128`;
            `k10:int128`;`k11:int128`;`k12:int128`;`k13:int128`;`k14:int128`;`h:int128`];;

let mk_wb_front_goal postcond =
  let ens = subst [wb_front_pre_tm,`PPP:armstate->bool`; postcond,`QQQ:armstate->bool`;
                   wb_front_frame_tm,`CCC:armstate->armstate->bool`]
              `ensures arm PPP QQQ CCC` in
  list_mk_forall(wb_front_vars, mk_imp(wb_front_hyps_tm, ens));;

(* Harvest all `read _ s = _` facts PLUS the aligned_bytes_loaded conjunct
   (WITHOUT it the back-leg tails cannot step: "ARM_CONV: can't find
   aligned_bytes_loaded"). *)
let build_state_postcond_tms2 sname (asl:term list) =
  let sv = mk_var(sname,`:armstate`) in
  let s = mk_var("s",`:armstate`) in
  let keep c =
    (is_eq c && (match lhs c with
       | Comb(Comb(Const("read",_),_),st) -> st = sv | _ -> false))
    || (match c with
        | Comb(Comb(Comb(Const("aligned_bytes_loaded",_),st),_),_) -> st = sv
        | _ -> false) in
  let kept = filter keep asl in
  let albl,reads = partition (fun c -> not(is_eq c)) kept in
  mk_abs(s, vsubst [s,sv] (end_itlist (curry mk_conj) (albl @ reads)));;

let wb_front_init_tac =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C_ARGUMENTS]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_dec]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check(is_conj o concl)) THEN
  WB_FRONT_PREP_BUF_TAC THEN WB_FRONT_STEP_TAC;;

(* The s265 postcondition, embedded as a fully-type-annotated literal so the
   front simulates ONCE (in the WB_FRONT_BUF proof) instead of twice (the old
   harvest pass re-ran the same 265-step sim, ~232s wasted per cold load).
   COMPACT FORM: the 8 in-flight keystream towers are folded to
   aes13 (gcm_ctr_inc^i ctr0) k0..k13 (GSYM aes13 + GSYM GCM_CTR_INCi_LANES),
   which shrinks the raw harvested term from ~83k to ~19k chars and makes the
   Q-register conjuncts readable.  The WB_FRONT_BUF proof applies the same fold
   to the simulated assumptions (wb_front_fold_tac) before final-state matching.
   REGENERATION (if the front or its keep-profile changes): re-enable the
   harvest pass below, fold with
     (REWRITE_CONV[GSYM aes13] THENC REWRITE_CONV(map GSYM wb_ctr_lanes_thms)),
   then print with print_types_of_subterms := 2 and replace every
   "(&:num->int)" with "(int_of_num:num->int)" (the bare & does not reparse);
   verify aconv against the folded harvested term.
     let wb_front_postcond_harvested =
       let min_goal = mk_wb_front_goal `\s:armstate. read PC s = word (pc + 3796)` in
       let _ = g min_goal in
       let _ = e wb_front_init_tac in
       let (asl265,_) = top_goal() in
       build_state_postcond_tms2 "s265" asl265;;  *)
let wb_ctr_lanes_thms =
  [GCM_CTR_INC_LANES; GCM_CTR_INC2_LANES; GCM_CTR_INC3_LANES; GCM_CTR_INC4_LANES;
   GCM_CTR_INC5_LANES; GCM_CTR_INC6_LANES; GCM_CTR_INC7_LANES];;
(* fold the raw simulated assumptions onto the compact postcondition shapes *)
let wb_front_fold_tac =
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM aes13]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE(map GSYM wb_ctr_lanes_thms));;
let wb_front_postcond = parse_term {|\(s:armstate).
    (aligned_bytes_loaded:armstate->(64)word->((8)word)list->bool)
    (s:armstate)
    ((word:num->(64)word) (pc:num))
    (aesv8_gcm_8x_dec_256_wb_mc:((8)word)list) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (PC:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) ((pc:num) + 3796) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q24:(armstate,(128)word)component)
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((polyval_dot:(128)word->(128)word->(128)word)
          ((polyval_dot:(128)word->(128)word->(128)word)
           ((byteswap128:(128)word->(128)word) (h:(128)word))
          ((byteswap128:(128)word->(128)word) (h:(128)word)))
         ((byteswap128:(128)word->(128)word) (h:(128)word)))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word)))))
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((polyval_dot:(128)word->(128)word->(128)word)
          ((byteswap128:(128)word->(128)word) (h:(128)word))
         ((byteswap128:(128)word->(128)word) (h:(128)word)))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q25:(armstate,(128)word)component)
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((polyval_dot:(128)word->(128)word->(128)word)
          ((polyval_dot:(128)word->(128)word->(128)word)
           ((byteswap128:(128)word->(128)word) (h:(128)word))
          ((byteswap128:(128)word->(128)word) (h:(128)word)))
         ((byteswap128:(128)word->(128)word) (h:(128)word)))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    ((read:(armstate,bool)component->armstate->bool)
     (NF:(armstate,bool)component)
     (s:armstate) <=>
     (ival:(64)word->int)
     ((word_sub:(64)word->(64)word->(64)word)
      ((word:num->(64)word) (16 * (nblk:num)))
     ((word:num->(64)word) 112)) <
     (int_of_num:num->int)0) /\
    ((read:(armstate,bool)component->armstate->bool)
     (ZF:(armstate,bool)component)
     (s:armstate) <=>
     (val:(64)word->num)
     ((word_sub:(64)word->(64)word->(64)word)
      ((word:num->(64)word) (16 * (nblk:num)))
     ((word:num->(64)word) 112)) =
     0) /\
    ((read:(armstate,bool)component->armstate->bool)
     (CF:(armstate,bool)component)
     (s:armstate) <=>
     112 <= (val:(64)word->num) ((word:num->(64)word) (16 * (nblk:num)))) /\
    ((read:(armstate,bool)component->armstate->bool)
     (VF:(armstate,bool)component)
     (s:armstate) <=>
     ~((ival:(64)word->int) ((word:num->(64)word) (16 * (nblk:num))) -
       (int_of_num:num->int)112 =
       (ival:(64)word->int)
       ((word_sub:(64)word->(64)word->(64)word)
        ((word:num->(64)word) (16 * (nblk:num)))
       ((word:num->(64)word) 112)))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q16:(armstate,(128)word)component)
    (s:armstate) =
    (word_subword:(256)word->num#num->(128)word)
    ((word_join:(128)word->(128)word->(256)word)
     ((word_bytereverse:(128)word->(128)word) (xi:(128)word))
    ((word_bytereverse:(128)word->(128)word) (xi:(128)word)))
    (64,128) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q7:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word))))))))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q6:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word)))))))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q0:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    (ctr0:(128)word)
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q1:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes64:(64)word->((64)word->(8)word,(64)word)component)
     ((word_add:(64)word->(64)word->(64)word) (stackpointer:(64)word)
     ((word:num->(64)word) 64)))
    (s:armstate) =
    (word:num->(64)word) 13979173243358019584 /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes64:(64)word->((64)word->(8)word,(64)word)component)
     ((word_add:(64)word->(64)word->(64)word) (stackpointer:(64)word)
     ((word:num->(64)word) 72)))
    (s:armstate) =
    (word:num->(64)word) 0 /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X11:(armstate,(64)word)component)
    (s:armstate) =
    (key_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X9:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) (16 * (nblk:num)) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (SP:(armstate,(64)word)component)
    (s:armstate) =
    (stackpointer:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X1:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) (128 * (nblk:num)) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X2:(armstate,(64)word)component)
    (s:armstate) =
    (out_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X3:(armstate,(64)word)component)
    (s:armstate) =
    (xi_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X6:(armstate,(64)word)component)
    (s:armstate) =
    (htbl_p:(64)word) /\
    (read:(armstate,num)component->armstate->num)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes:(64)word#num->((64)word->(8)word,num)component)
     ((in_p:(64)word),16 * (nblk:num)))
    (s:armstate) =
    (num_of_bytelist:((8)word)list->num) (ibytes:((8)word)list) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     (xi_p:(64)word))
    (s:armstate) =
    (xi:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     (ivec_p:(64)word))
    (s:armstate) =
    (ctr0:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     (key_p:(64)word))
    (s:armstate) =
    (k0:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 16)))
    (s:armstate) =
    (k1:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 32)))
    (s:armstate) =
    (k2:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 48)))
    (s:armstate) =
    (k3:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 64)))
    (s:armstate) =
    (k4:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 80)))
    (s:armstate) =
    (k5:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 96)))
    (s:armstate) =
    (k6:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 112)))
    (s:armstate) =
    (k7:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 128)))
    (s:armstate) =
    (k8:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 144)))
    (s:armstate) =
    (k9:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 160)))
    (s:armstate) =
    (k10:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 176)))
    (s:armstate) =
    (k11:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 192)))
    (s:armstate) =
    (k12:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 208)))
    (s:armstate) =
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 224)))
    (s:armstate) =
    (k14:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     (htbl_p:(64)word))
    (s:armstate) =
    (h:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 16)))
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((byteswap128:(128)word->(128)word) (h:(128)word))
    ((byteswap128:(128)word->(128)word) (h:(128)word)))))
    ((karatsuba_mid:(128)word->(64)word) (h:(128)word)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 32)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((byteswap128:(128)word->(128)word) (h:(128)word))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 48)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((byteswap128:(128)word->(128)word) (h:(128)word))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 64)))
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((byteswap128:(128)word->(128)word) (h:(128)word))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word)))))
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((byteswap128:(128)word->(128)word) (h:(128)word))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 80)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((byteswap128:(128)word->(128)word) (h:(128)word))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 96)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((byteswap128:(128)word->(128)word) (h:(128)word))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 112)))
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((byteswap128:(128)word->(128)word) (h:(128)word))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word)))))
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((byteswap128:(128)word->(128)word) (h:(128)word))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 128)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((byteswap128:(128)word->(128)word) (h:(128)word))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 144)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((polyval_dot:(128)word->(128)word->(128)word)
          ((byteswap128:(128)word->(128)word) (h:(128)word))
         ((byteswap128:(128)word->(128)word) (h:(128)word)))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 160)))
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((polyval_dot:(128)word->(128)word->(128)word)
          ((polyval_dot:(128)word->(128)word->(128)word)
           ((byteswap128:(128)word->(128)word) (h:(128)word))
          ((byteswap128:(128)word->(128)word) (h:(128)word)))
         ((byteswap128:(128)word->(128)word) (h:(128)word)))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word)))))
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((polyval_dot:(128)word->(128)word->(128)word)
          ((byteswap128:(128)word->(128)word) (h:(128)word))
         ((byteswap128:(128)word->(128)word) (h:(128)word)))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 176)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((polyval_dot:(128)word->(128)word->(128)word)
          ((polyval_dot:(128)word->(128)word->(128)word)
           ((byteswap128:(128)word->(128)word) (h:(128)word))
          ((byteswap128:(128)word->(128)word) (h:(128)word)))
         ((byteswap128:(128)word->(128)word) (h:(128)word)))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     (in_p:(64)word))
    (s:armstate) =
    (bytes_to_int128:((8)word)list->(128)word)
    ((SUB_LIST:num#num->((8)word)list->((8)word)list) (0,16)
    (ibytes:((8)word)list)) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X16:(armstate,(64)word)component)
    (s:armstate) =
    (ivec_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X10:(armstate,(64)word)component)
    (s:armstate) =
    (word_add:(64)word->(64)word->(64)word) (stackpointer:(64)word)
    ((word:num->(64)word) 64) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X15:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) 4294967296 /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q31:(armstate,(128)word)component)
    (s:armstate) =
    (word:num->(128)word) 79228162514264337593543950336 /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q19:(armstate,(128)word)component)
    (s:armstate) =
    (word_bytereverse:(128)word->(128)word) (xi:(128)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X4:(armstate,(64)word)component)
    (s:armstate) =
    (word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
    ((word:num->(64)word) (16 * (nblk:num))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q27:(armstate,(128)word)component)
    (s:armstate) =
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q26:(armstate,(128)word)component)
    (s:armstate) =
    (k12:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q28:(armstate,(128)word)component)
    (s:armstate) =
    (k14:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q5:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word))))))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q2:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word)))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q4:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word)))))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q3:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word))))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X5:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) (16 * (nblk:num)) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X0:(armstate,(64)word)component)
    (s:armstate) =
    (word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
    ((word:num->(64)word) 16) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q9:(armstate,(128)word)component)
    (s:armstate) =
    (bytes_to_int128:((8)word)list->(128)word)
    ((SUB_LIST:num#num->((8)word)list->((8)word)list) (0,16)
    (ibytes:((8)word)list))|};;

(* THE SHARED FRONT LEMMA. *)
let WB_FRONT_BUF = prove(mk_wb_front_goal wb_front_postcond,
  wb_front_init_tac THEN wb_front_fold_tac THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC);;

(* ---- buffer-form band statements ------------------------------------------ *)
let mk_cph i = subst [mk_small_numeral(16*i),`nnn:num`]
  `bytes_to_int128 (SUB_LIST (nnn,16) (ibytes:byte list))`;;
let mk_ctr i =
  let rec go n = if n = 0 then `ctr0:int128`
    else mk_comb(`gcm_ctr_inc`, go (n-1)) in go i;;
let mk_outp_read i =
  let addr = if i = 0 then `out_p:int64`
    else subst [mk_small_numeral(16*i),`nnn:num`] `word_add out_p (word nnn):int64` in
  subst [addr,`aaa:int64`] `read (memory :> bytes128 (aaa:int64)) s:int128`;;
let mk_out_conj i =
  mk_eq(mk_outp_read i,
    subst [mk_cph i,`ccc:int128`; mk_ctr i,`ttt:int128`]
      `word_xor (ccc:int128) (aes256_encrypt (ttt:int128)
        [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`);;
let mk_ghash_list k =
  mk_flist(map (fun i -> mk_comb(`word_bytereverse:int128->int128`, mk_cph i)) (0--(k-1)));;

let mk_band_goal k =
  let n16 = mk_small_numeral(16*k) and n128 = mk_small_numeral(128*k) in
  let hyps = subst [n16,`sss:num`]
    `LENGTH (ibytes:byte list) = sss /\
     aligned 16 stackpointer /\
     nonoverlapping (word pc, 4560) (stackpointer:int64, 80) /\
     nonoverlapping (word pc, 4560) (out_p:int64, sss) /\
     nonoverlapping (word pc, 4560) (xi_p:int64, 16) /\
     nonoverlapping (word pc, 4560) (ivec_p:int64, 16) /\
     nonoverlapping (out_p, sss) (xi_p, 16) /\
     nonoverlapping (out_p, sss) (ivec_p, 16) /\
     nonoverlapping (xi_p, 16) (ivec_p, 16) /\
     nonoverlapping (ivec_p, 16) (in_p:int64, sss) /\
     nonoverlapping (ivec_p, 16) (key_p:int64, 240) /\
     nonoverlapping (ivec_p, 16) (htbl_p:int64, 192) /\
     nonoverlapping (in_p, sss) (stackpointer, 80) /\
     nonoverlapping (key_p, 240) (stackpointer, 80) /\
     nonoverlapping (htbl_p, 192) (stackpointer, 80) /\
     nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
     nonoverlapping (xi_p, 16) (in_p, sss) /\
     nonoverlapping (xi_p, 16) (key_p, 240) /\
     nonoverlapping (xi_p, 16) (htbl_p, 192) /\
     nonoverlapping (xi_p, 16) (stackpointer, 80) /\
     nonoverlapping (out_p, sss) (in_p, sss) /\
     nonoverlapping (out_p, sss) (key_p, 240) /\
     nonoverlapping (out_p, sss) (htbl_p, 192) /\
     nonoverlapping (out_p, sss) (stackpointer, 80)` in
  let pre = subst [n16,`sss:num`; n128,`bbb:num`]
    `\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
        read PC s = word (pc + 0x20) /\ read SP s = stackpointer /\
        C_ARGUMENTS [in_p; word bbb; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
        read (memory :> bytes (in_p, sss)) s = num_of_bytelist ibytes /\
        read (memory :> bytes128 xi_p) s = xi /\
        read (memory :> bytes128 ivec_p) s = ctr0 /\
        read (memory :> bytes128 key_p) s = k0 /\
        read (memory :> bytes128 (word_add key_p (word 16))) s = k1 /\
        read (memory :> bytes128 (word_add key_p (word 32))) s = k2 /\
        read (memory :> bytes128 (word_add key_p (word 48))) s = k3 /\
        read (memory :> bytes128 (word_add key_p (word 64))) s = k4 /\
        read (memory :> bytes128 (word_add key_p (word 80))) s = k5 /\
        read (memory :> bytes128 (word_add key_p (word 96))) s = k6 /\
        read (memory :> bytes128 (word_add key_p (word 112))) s = k7 /\
        read (memory :> bytes128 (word_add key_p (word 128))) s = k8 /\
        read (memory :> bytes128 (word_add key_p (word 144))) s = k9 /\
        read (memory :> bytes128 (word_add key_p (word 160))) s = k10 /\
        read (memory :> bytes128 (word_add key_p (word 176))) s = k11 /\
        read (memory :> bytes128 (word_add key_p (word 192))) s = k12 /\
        read (memory :> bytes128 (word_add key_p (word 208))) s = k13 /\
        read (memory :> bytes128 (word_add key_p (word 224))) s = k14 /\
        htable_mem_dec h htbl_p s` in
  let pc_post = `read PC s = word (pc + 4528)` in
  let outs = map mk_out_conj (0--(k-1)) in
  let xi_post = subst [mk_ghash_list k,`lll:int128 list`]
    `read (memory :> bytes128 xi_p) s =
     word_bytereverse
       (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi) (lll:int128 list))` in
  let post = mk_abs(`s:armstate`, end_itlist (curry mk_conj) (pc_post :: outs @ [xi_post])) in
  let frame = subst [n16,`sss:num`]
    `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [memory :> bytes(out_p:int64, sss); memory :> bytes(xi_p:int64, 16);
                memory :> bytes(ivec_p:int64, 16);
                memory :> bytes(stackpointer:int64, 80)] ,,
     MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31]` in
  let ens = subst [pre,`PPP:armstate->bool`; post,`QQQ:armstate->bool`;
                   frame,`CCC:armstate->armstate->bool`] `ensures arm PPP QQQ CCC` in
  let vars = subtract wb_front_vars [`nblk:num`] in
  list_mk_forall(vars, mk_imp(hyps, ens));;

(* ---- recomposition machinery ---------------------------------------------- *)
let arith_16k k = ARITH_RULE(mk_eq(mk_binop `( * ):num->num->num` `16` (mk_small_numeral k),
                                   mk_small_numeral(16*k)));;
let arith_128k k = ARITH_RULE(mk_eq(mk_binop `( * ):num->num->num` `128` (mk_small_numeral k),
                                    mk_small_numeral(128*k)));;
(* front lemma instantiated at nblk:=k, arithmetic normalized *)
let wbf_at k = REWRITE_RULE[arith_16k k; arith_128k k]
  (SPECL [`pc:num`;`stackpointer:int64`;`out_p:int64`;`xi_p:int64`;`ivec_p:int64`;
          `in_p:int64`;`key_p:int64`;`htbl_p:int64`; mk_small_numeral k;
          `ibytes:byte list`;`xi:int128`;`ctr0:int128`;`k0:int128`;`k1:int128`;
          `k2:int128`;`k3:int128`;`k4:int128`;`k5:int128`;`k6:int128`;`k7:int128`;
          `k8:int128`;`k9:int128`;`k10:int128`;`k11:int128`;`k12:int128`;
          `k13:int128`;`k14:int128`;`h:int128`] WB_FRONT_BUF);;
(* intermediate assertion = WB_FRONT_BUF's postcond @ nblk:=k, normalized *)
let q_at k = rhs(concl(REWRITE_CONV[arith_16k k; arith_128k k]
  (vsubst [mk_small_numeral k,`nblk:num`] wb_front_postcond)));;
(* doubled frame for ENSURES_FRAME_SUBSUMED (F ,, F subsumes to F) *)
let fdbl_at k =
  let fs = subst [mk_small_numeral(16*k),`sss:num`]
    `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [memory :> bytes(out_p:int64, sss); memory :> bytes(xi_p:int64, 16);
                memory :> bytes(ivec_p:int64, 16); memory :> bytes(stackpointer:int64, 80)] ,,
     MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31]` in
  mk_binop `(,,):(armstate->armstate->bool)->(armstate->armstate->bool)->(armstate->armstate->bool)` fs fs;;

(* h-power towers: dot j = polyval_dot^(j-1) over byteswap128 h *)
let rec hdot j = if j = 1 then `byteswap128 h`
  else mk_comb(mk_comb(`polyval_dot:int128->int128->int128`, hdot (j-1)), `byteswap128 h`);;
let mk_habbrev j =
  let hv = mk_var("h"^string_of_int j, `:int128`) in
  ABBREV_TAC (mk_eq(hv, mk_comb(`byteswap128:int128->int128`, hdot j))) THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`byteswap128:int128->int128`, hv), hdot j)) ASSUME_TAC THENL
  [EXPAND_TAC ("h"^string_of_int j) THEN REWRITE_TAC[BYTESWAP128_INVOLUTION]; ALL_TAC];;

(* Back-leg prep for band k: init at the s265 assertion, concretize the flags,
   derive input lanes 1..k-1, abbreviate cph names + h powers so the verbatim
   wb.ml tails apply unchanged. *)
let WB_PREP_TAC k =
  let n16 = mk_small_numeral(16*k) in
  let lanes =
    if k = 1 then ALL_TAC else
    SUBGOAL_THEN (subst [mk_small_numeral k,`kkk:num`]
      `!i. i < kkk ==> read (memory :> bytes128 (word_add in_p (word (16 * i)))) s265 =
              bytes_to_int128 (SUB_LIST (16 * i, 16) (ibytes:byte list))`)
      MP_TAC THENL
    [MATCH_MP_TAC INPUT_BYTES_TO_BYTE128_LANES THEN
     SUBGOAL_THEN (subst [n16,`sss:num`] `SUB_LIST (0,sss) (ibytes:byte list) = ibytes`)
       (fun th -> ASM_REWRITE_TAC[th; LE_REFL;
          ARITH_RULE(mk_eq(mk_binop `( * ):num->num->num` `16` (mk_small_numeral k), n16))]) THEN
     MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN ASM_REWRITE_TAC[LE_REFL];
     DISCH_THEN(fun lth ->
       EVERY(map (fun i ->
         ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_RED_CONV)
           (MP (SPEC (mk_small_numeral i) lth)
               (ARITH_RULE(mk_binop `(<):num->num->bool` (mk_small_numeral i) (mk_small_numeral k))))))
         (1--(k-1))))] in
  let cphs =
    if k = 1 then ABBREV_TAC (mk_eq(`cph:int128`, mk_cph 0))
    else EVERY(map (fun i ->
      ABBREV_TAC (mk_eq(mk_var("cph"^string_of_int i,`:int128`), mk_cph i))) (0--(k-1))) in
  let habbrevs = if k = 1 then ALL_TAC else EVERY(map mk_habbrev (2--k)) in
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN ENSURES_INIT_TAC "s265" THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV WORD_REDUCE_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  lanes THEN cphs THEN habbrevs;;

(* The band prover: split at pc+3796 via FRAME_SUBSUMED + TRANS
   (ENSURES_SEQUENCE_TAC throws MAYCHANGE_IDEMPOT on this frame), discharge
   the front leg with WB_FRONT_BUF, then prep + the band's verbatim tail. *)
let prove_band k tail_tac =
  prove(mk_band_goal k,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC (fdbl_at k) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC ENSURES_TRANS THEN EXISTS_TAC (q_at k) THEN CONJ_TAC THENL
     [MATCH_MP_TAC (wbf_at k) THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    WB_PREP_TAC k THEN tail_tac);;

(* ---- the 8 recomposed bands ----------------------------------------------- *)
let AESV8_GCM_8X_DEC_256_WB_BUF_1BLOCK = prove_band 1 WB_TAIL_1_TAC;;
let AESV8_GCM_8X_DEC_256_WB_BUF_2BLOCK = prove_band 2 WB_TAIL_2_TAC;;
let AESV8_GCM_8X_DEC_256_WB_BUF_3BLOCK = prove_band 3 WB_TAIL_3_TAC;;
let AESV8_GCM_8X_DEC_256_WB_BUF_4BLOCK = prove_band 4 WB_TAIL_4_TAC;;
let AESV8_GCM_8X_DEC_256_WB_BUF_5BLOCK = prove_band 5 WB_TAIL_5_TAC;;
let AESV8_GCM_8X_DEC_256_WB_BUF_6BLOCK = prove_band 6 WB_TAIL_6_TAC;;
let AESV8_GCM_8X_DEC_256_WB_BUF_7BLOCK = prove_band 7 WB_TAIL_7_TAC;;
let AESV8_GCM_8X_DEC_256_WB_BUF_8BLOCK = prove_band 8 WB_TAIL_8_TAC;;


(* ------------------------------------------------------------------------- *)
(* Readable byte_list_at wrappers + the <=8-block dispatch theorem.           *)
(* Sim-free from the BUF band theorems: only the input/output presentations   *)
(* change, discharged by ARM-free bridges via ENSURES_PRE/POSTCONDITION_THM.  *)
(* Together with AESV8_GCM_8X_DEC_256_WB_GUARD (above) this is the complete   *)
(* contract of the whole-blocks binary: valid bit_len = 128*nblk (1<=nblk<=8) *)
(* -> DISPATCH; invalid bit_len -> GUARD (ret 0, no memory).                  *)
(* ------------------------------------------------------------------------- *)

(* ---- step 1: input bridge (byte_list_at -> whole-buffer bytes read) -------- *)
let BYTE_LIST_AT_TO_READ_BYTES = prove
 (`!bl (ptr:int64) (len:int64) s.
    byte_list_at bl ptr len s /\ LENGTH bl = val len
    ==> read (memory :> bytes (ptr, val len)) s = num_of_bytelist bl`,
  REPEAT GEN_TAC THEN REWRITE_TAC[byte_list_at] THEN STRIP_TAC THEN
  SUBGOAL_THEN `num_of_bytelist (bl:byte list) = num_of_bytelist (SUB_LIST (0, val (len:int64)) bl)` SUBST1_TAC THENL
   [AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`val (len:int64)`; `ptr:int64`; `bl:byte list`; `s:armstate`] BYTE_LIST_TO_NUM_THM) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN DISCH_THEN(fun th -> ASM_REWRITE_TAC[GSYM th]));;

(* ---- step 2: whole-blocks output bridge (per-block stores -> byte_list_at).
   Whole-blocks analogue of BYTE_LIST_AT_NBLOCK_CTR: specialize at tail=16 via
   AES_CTR_FULL_TAIL_BYTES_WHOLE; the all-ones mask makes outprev irrelevant
   (word 0 witness). *)
let BYTE_LIST_AT_WHOLE_CTR = prove
 (`!ctr0 pts keys n out_p (len:int64) s.
    1 <= n /\ n = LENGTH pts /\ val len = 16 * n /\
    (!j. j < n ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                   EL j (aes_ctr ctr0 pts keys))
    ==> byte_list_at (aes_ctr_bytes ctr0 pts keys) out_p len s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `aes_ctr_bytes ctr0 pts keys = aes_ctr_full_tail_bytes ctr0 pts keys (n - 1) 16` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC AES_CTR_FULL_TAIL_BYTES_WHOLE THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC BYTE_LIST_AT_NBLOCK_CTR THEN
  EXISTS_TAC `word 0:int128` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    ARITH_TAC;
    ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[WORD_AND_ALLONES_128] THEN
    REWRITE_TAC[WORD_RULE `word_xor x (word_and (word 0) y) = x`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

(* ---- step 3: per-band EL facts builder (generalizes the hand AES_CTR_k_EL). *)
let build_aes_ctr_el k =
  let pts = map (fun i -> mk_var("pt"^string_of_int i,`:int128`)) (0--(k-1)) in
  let plist = mk_flist pts in
  let rec ctr j = if j = 0 then `ctr0:int128` else mk_comb(`gcm_ctr_inc`, ctr (j-1)) in
  let conj_of j =
    mk_eq(list_mk_comb(`EL:num->(int128)list->int128`,
            [mk_small_numeral j;
             list_mk_comb(`aes_ctr`, [`ctr0:int128`; plist; `keys:int128 list`])]),
          list_mk_comb(`word_xor:int128->int128->int128`,
            [el j pts;
             list_mk_comb(`aes256_encrypt`, [ctr j; `keys:int128 list`])])) in
  let goal = list_mk_conj (map conj_of (0--(k-1))) in
  let sucs = map (fun i -> num_CONV (mk_small_numeral i)) (1--(k-1)) in
  prove(goal,
    REWRITE_TAC[aes_ctr; aes_ctr_rec; aes_ctr_block; gcm_ctr_inc_iter] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC(sucs @ [EL; HD; TL]) THEN
    REWRITE_TAC[gcm_ctr_inc_iter] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC(sucs @ [gcm_ctr_inc_iter]) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC(sucs @ [gcm_ctr_inc_iter]));;

(* ---- step 4: wrapper goal builder + prover ---------------------------------
   Wrapper = BUF band statement with (a) the input buffer read replaced by
   byte_list_at ibytes, (b) the postcondition per-block stores + explicit GHASH
   replaced by gcm_dec_pt_bytes / gcm_dec_final_xi over the whole buffer.
   Sim-free: PRE via BYTE_LIST_AT_TO_READ_BYTES, POST via BYTE_LIST_AT_WHOLE_CTR
   + the per-band EL facts; the spec unfolds via GCM_DEC_*_WHOLE_k. *)
let wb_keys_tm = `[k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]`;;
let mk_wb_wrapper_goal k =
  let g = mk_band_goal k in
  let vars, body = strip_forall g in
  let hyps, ens = dest_imp body in
  let frame = rand ens and post = rand(rator ens) and pre = rand(rator(rator ens)) in
  let n16 = mk_small_numeral(16*k) in
  let sv = `s:armstate` in
  let oldread = subst [n16,`nnn:num`]
    `read (memory :> bytes (in_p,nnn)) s = num_of_bytelist (ibytes:byte list)` in
  let newread = subst [n16,`nnn:num`]
    `byte_list_at (ibytes:byte list) in_p (word nnn) s` in
  let pre_body = snd(dest_abs pre) in
  let pre' = mk_abs(sv, list_mk_conj
    (map (fun c -> if c = oldread then newread else c) (conjuncts pre_body))) in
  let post_body = snd(dest_abs post) in
  let pcc = hd(conjuncts post_body) in
  let outpost = subst [n16,`nnn:num`; wb_keys_tm,`kl:int128 list`]
    `byte_list_at (gcm_dec_pt_bytes nnn ibytes ctr0 (kl:int128 list)) out_p (word nnn) s` in
  let xipost = subst [n16,`nnn:num`]
    `read (memory :> bytes128 xi_p) s = gcm_dec_final_xi nnn ibytes xi h` in
  let post' = mk_abs(sv, list_mk_conj [pcc; outpost; xipost]) in
  list_mk_forall(vars,
    mk_imp(hyps, list_mk_comb(rator(rator(rator ens)), [pre'; post'; frame])));;

let ghash_wholes = [GCM_DEC_GHASH_BLOCKS_WHOLE_1;GCM_DEC_GHASH_BLOCKS_WHOLE_2;
                    GCM_DEC_GHASH_BLOCKS_WHOLE_3;GCM_DEC_GHASH_BLOCKS_WHOLE_4;
                    GCM_DEC_GHASH_BLOCKS_WHOLE_5;GCM_DEC_GHASH_BLOCKS_WHOLE_6;
                    GCM_DEC_GHASH_BLOCKS_WHOLE_7;GCM_DEC_GHASH_BLOCKS_WHOLE_8];;
let pt_wholes = [GCM_DEC_PT_BYTES_WHOLE_1;GCM_DEC_PT_BYTES_WHOLE_2;
                 GCM_DEC_PT_BYTES_WHOLE_3;GCM_DEC_PT_BYTES_WHOLE_4;
                 GCM_DEC_PT_BYTES_WHOLE_5;GCM_DEC_PT_BYTES_WHOLE_6;
                 GCM_DEC_PT_BYTES_WHOLE_7;GCM_DEC_PT_BYTES_WHOLE_8];;
let prove_wb_wrapper k buf_thm =
  let n16 = mk_small_numeral(16*k) in
  let band = mk_band_goal k in
  let _, bbody = strip_forall band in
  let _, bens = dest_imp bbody in
  let pre_buf = rand(rator(rator bens)) and post_buf = rand(rator bens) in
  let el_facts = build_aes_ctr_el k in
  let inbridge = CONV_RULE (ONCE_DEPTH_CONV WORD_REDUCE_CONV)
    (SPECL [`ibytes:byte list`;`in_p:int64`; mk_comb(`word:num->int64`,n16); `s:armstate`]
       BYTE_LIST_AT_TO_READ_BYTES) in
  let jsplit = ARITH_RULE
    (mk_eq(subst [mk_small_numeral k,`kkk:num`] `j < kkk:num`,
           list_mk_disj (map (fun i -> mk_eq(`j:num`, mk_small_numeral i)) (0--(k-1))))) in
  prove(mk_wb_wrapper_goal k,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[gcm_dec_final_xi; el (k-1) ghash_wholes; el (k-1) pt_wholes; MAP] THEN
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
    EXISTS_TAC pre_buf THEN
    CONJ_TAC THENL
     [X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC inbridge THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
      EXISTS_TAC post_buf THEN
      CONJ_TAC THENL
       [X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC BYTE_LIST_AT_WHOLE_CTR THEN
        EXISTS_TAC (mk_small_numeral k) THEN
        REPEAT CONJ_TAC THENL
         [ARITH_TAC;
          REWRITE_TAC[LENGTH] THEN ARITH_TAC;
          CONV_TAC WORD_REDUCE_CONV THEN ARITH_TAC;
          X_GEN_TAC `j:num` THEN REWRITE_TAC[jsplit] THEN
          STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
          CONV_TAC NUM_REDUCE_CONV THEN
          REWRITE_TAC[WORD_ADD_0; el_facts] THEN ASM_REWRITE_TAC[el_facts]];
        MATCH_MP_TAC buf_thm THEN ASM_REWRITE_TAC[]]]);;

(* ---- the 8 readable byte_list_at band wrappers ----------------------------- *)
let AESV8_GCM_8X_DEC_256_WB_1BLOCK = prove_wb_wrapper 1 AESV8_GCM_8X_DEC_256_WB_BUF_1BLOCK;;
let AESV8_GCM_8X_DEC_256_WB_2BLOCK = prove_wb_wrapper 2 AESV8_GCM_8X_DEC_256_WB_BUF_2BLOCK;;
let AESV8_GCM_8X_DEC_256_WB_3BLOCK = prove_wb_wrapper 3 AESV8_GCM_8X_DEC_256_WB_BUF_3BLOCK;;
let AESV8_GCM_8X_DEC_256_WB_4BLOCK = prove_wb_wrapper 4 AESV8_GCM_8X_DEC_256_WB_BUF_4BLOCK;;
let AESV8_GCM_8X_DEC_256_WB_5BLOCK = prove_wb_wrapper 5 AESV8_GCM_8X_DEC_256_WB_BUF_5BLOCK;;
let AESV8_GCM_8X_DEC_256_WB_6BLOCK = prove_wb_wrapper 6 AESV8_GCM_8X_DEC_256_WB_BUF_6BLOCK;;
let AESV8_GCM_8X_DEC_256_WB_7BLOCK = prove_wb_wrapper 7 AESV8_GCM_8X_DEC_256_WB_BUF_7BLOCK;;
let AESV8_GCM_8X_DEC_256_WB_8BLOCK = prove_wb_wrapper 8 AESV8_GCM_8X_DEC_256_WB_BUF_8BLOCK;;

(* ---- step 5: the <=8-block dispatch theorem --------------------------------
   ONE readable theorem for every valid whole-blocks call: symbolic nblk
   (1 <= nblk <= 8), bit_len C-argument = word (128*nblk), byte_list_at in/out
   over the whole 16*nblk-byte buffer, postcondition via the recursive specs
   gcm_dec_pt_bytes / gcm_dec_final_xi.  Proof: 8-way case split on nblk, each
   case reduces 16*k/128*k to numerals and MATCH_MP_TACs the band wrapper.
   Combined with AESV8_GCM_8X_DEC_256_WB_GUARD (wb.ml) this is the complete
   contract of the whole-blocks binary. *)
let mk_wb_dispatch_goal () =
  let n16 = `16 * nblk` and n128 = `128 * nblk` in
  let hyps0 = subst [n16,`sss:num`]
    `LENGTH (ibytes:byte list) = sss /\
     aligned 16 stackpointer /\
     nonoverlapping (word pc, 4560) (stackpointer:int64, 80) /\
     nonoverlapping (word pc, 4560) (out_p:int64, sss) /\
     nonoverlapping (word pc, 4560) (xi_p:int64, 16) /\
     nonoverlapping (word pc, 4560) (ivec_p:int64, 16) /\
     nonoverlapping (out_p, sss) (xi_p, 16) /\
     nonoverlapping (out_p, sss) (ivec_p, 16) /\
     nonoverlapping (xi_p, 16) (ivec_p, 16) /\
     nonoverlapping (ivec_p, 16) (in_p:int64, sss) /\
     nonoverlapping (ivec_p, 16) (key_p:int64, 240) /\
     nonoverlapping (ivec_p, 16) (htbl_p:int64, 192) /\
     nonoverlapping (in_p, sss) (stackpointer, 80) /\
     nonoverlapping (key_p, 240) (stackpointer, 80) /\
     nonoverlapping (htbl_p, 192) (stackpointer, 80) /\
     nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
     nonoverlapping (xi_p, 16) (in_p, sss) /\
     nonoverlapping (xi_p, 16) (key_p, 240) /\
     nonoverlapping (xi_p, 16) (htbl_p, 192) /\
     nonoverlapping (xi_p, 16) (stackpointer, 80) /\
     nonoverlapping (out_p, sss) (in_p, sss) /\
     nonoverlapping (out_p, sss) (key_p, 240) /\
     nonoverlapping (out_p, sss) (htbl_p, 192) /\
     nonoverlapping (out_p, sss) (stackpointer, 80)` in
  let hyps = mk_conj(`1 <= nblk`, mk_conj(`nblk <= 8`, hyps0)) in
  let pre = subst [n16,`sss:num`; n128,`bbb:num`]
    `\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
        read PC s = word (pc + 0x20) /\ read SP s = stackpointer /\
        C_ARGUMENTS [in_p; word bbb; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
        byte_list_at (ibytes:byte list) in_p (word sss) s /\
        read (memory :> bytes128 xi_p) s = xi /\
        read (memory :> bytes128 ivec_p) s = ctr0 /\
        read (memory :> bytes128 key_p) s = k0 /\
        read (memory :> bytes128 (word_add key_p (word 16))) s = k1 /\
        read (memory :> bytes128 (word_add key_p (word 32))) s = k2 /\
        read (memory :> bytes128 (word_add key_p (word 48))) s = k3 /\
        read (memory :> bytes128 (word_add key_p (word 64))) s = k4 /\
        read (memory :> bytes128 (word_add key_p (word 80))) s = k5 /\
        read (memory :> bytes128 (word_add key_p (word 96))) s = k6 /\
        read (memory :> bytes128 (word_add key_p (word 112))) s = k7 /\
        read (memory :> bytes128 (word_add key_p (word 128))) s = k8 /\
        read (memory :> bytes128 (word_add key_p (word 144))) s = k9 /\
        read (memory :> bytes128 (word_add key_p (word 160))) s = k10 /\
        read (memory :> bytes128 (word_add key_p (word 176))) s = k11 /\
        read (memory :> bytes128 (word_add key_p (word 192))) s = k12 /\
        read (memory :> bytes128 (word_add key_p (word 208))) s = k13 /\
        read (memory :> bytes128 (word_add key_p (word 224))) s = k14 /\
        htable_mem_dec h htbl_p s` in
  let post = subst [n16,`sss:num`; wb_keys_tm,`kl:int128 list`]
    `\s. read PC s = word (pc + 4528) /\
         byte_list_at (gcm_dec_pt_bytes sss ibytes ctr0 (kl:int128 list)) out_p (word sss) s /\
         read (memory :> bytes128 xi_p) s = gcm_dec_final_xi sss ibytes xi h` in
  let frame = subst [n16,`sss:num`]
    `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [memory :> bytes(out_p:int64, sss); memory :> bytes(xi_p:int64, 16);
                memory :> bytes(ivec_p:int64, 16);
                memory :> bytes(stackpointer:int64, 80)] ,,
     MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31]` in
  let ens = subst [pre,`PPP:armstate->bool`; post,`QQQ:armstate->bool`;
                   frame,`CCC:armstate->armstate->bool`] `ensures arm PPP QQQ CCC` in
  list_mk_forall(wb_front_vars, mk_imp(hyps, ens));;

let AESV8_GCM_8X_DEC_256_WB_DISPATCH =
  let wrappers = [AESV8_GCM_8X_DEC_256_WB_1BLOCK;AESV8_GCM_8X_DEC_256_WB_2BLOCK;
                  AESV8_GCM_8X_DEC_256_WB_3BLOCK;AESV8_GCM_8X_DEC_256_WB_4BLOCK;
                  AESV8_GCM_8X_DEC_256_WB_5BLOCK;AESV8_GCM_8X_DEC_256_WB_6BLOCK;
                  AESV8_GCM_8X_DEC_256_WB_7BLOCK;AESV8_GCM_8X_DEC_256_WB_8BLOCK] in
  let case_tac =
    CONV_TAC NUM_REDUCE_CONV THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    FIRST (map (fun w -> MATCH_MP_TAC w THEN ASM_REWRITE_TAC[]) wrappers) in
  prove(mk_wb_dispatch_goal (),
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `nblk = 1 \/ nblk = 2 \/ nblk = 3 \/ nblk = 4 \/ nblk = 5 \/ nblk = 6 \/ nblk = 7 \/ nblk = 8`
      MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN case_tac);;
