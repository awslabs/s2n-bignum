(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The layout of mlkem-native's libmlkem.so compiled by gcc 12 with -O2 (see *)
(* mlkem_native/README.md): the addresses in the binary, as offsets from the *)
(* start of the image, that the proofs refer to, as names for                *)
(* common/layout.ml. The proofs use only these names, never the addresses    *)
(* themselves.                                                               *)
(*                                                                           *)
(* This file is maintained by hand for now. The values are those of the      *)
(* symbol table, the dynamic relocations and the disassembly of the binary.  *)
(*                                                                           *)
(* Functions are named after their symbols, without a suffix such as         *)
(* ".constprop.0" that GCC adds to a specialized copy, and with any other    *)
(* dots replaced by underscores. A function f has the names f for its        *)
(* address and f_size for its size. A label l inside it has the name f_l for *)
(* its address. The labels are named after the structure of the code:        *)
(*                                                                           *)
(*  - loopK is the header of the K-th loop of the function, counting the     *)
(*    natural loops (found from the dominators of the control flow graph) by *)
(*    the address of the header;                                             *)
(*  - loopK_test is the instruction before a conditional branch out of the   *)
(*    loop (usually the comparison that sets the flags for it), loopK_next   *)
(*    is the instruction after such a branch if it is inside the loop, and   *)
(*    loopK_back is the branch back to the header; these have a further      *)
(*    number if the loop has several such branches;                          *)
(*  - loopK_exit is the target of the branches out of the loop;              *)
(*  - joinK is the K-th instruction outside the loops with more than one     *)
(*    predecessor in the control flow graph;                                 *)
(*  - after_g is the instruction after the call of g, numbered if there are  *)
(*    several calls of g;                                                    *)
(*  - ret is the return instruction, and adrpK the K-th ADRP instruction.    *)
(*                                                                           *)
(* For a function that is also transcribed on its own in mlkem_native/*.S,   *)
(* with its code at its own pc, the names c_size and c_l are the size and    *)
(* the offset of the label l from the start of the function, where c is the  *)
(* symbol of the transcription without the prefix mlkem_native_ and the      *)
(* suffix for the compiler, e.g. poly_ntt_loop1 for the transcription        *)
(* mlkem_native_poly_ntt_gcc12_O2 of mlkem_poly_ntt.                         *)
(* ========================================================================= *)

needs "common/layout.ml";;

(* ------------------------------------------------------------------------- *)
(* The image, from address 0 up to the end of the read-only data.            *)
(* ------------------------------------------------------------------------- *)

install_layout ["libmlkem_size",0x6480];;

(* ------------------------------------------------------------------------- *)
(* The functions, as (name, address, size).                                  *)
(* ------------------------------------------------------------------------- *)

install_layout (layout_objects [
  "mlkem1024_gen_matrix",                            0x0850, 0x14c;
  "mlkem1024_indcpa_keypair_derand",                 0x09a0, 0x238;
  "mlkem1024_indcpa_enc",                            0x0be0, 0x2c8;
  "mlkem1024_indcpa_dec",                            0x0eb0, 0x158;
  "mlkem1024_check_pk",                              0x1010, 0x138;
  "mlkem1024_check_sk",                              0x1150, 0x0e8;
  "mlkem1024_keypair_derand",                        0x1240, 0x094;
  "mlkem1024_keypair",                               0x12d4, 0x08c;
  "mlkem1024_enc_derand",                            0x1360, 0x0e0;
  "mlkem1024_enc",                                   0x1440, 0x098;
  "mlkem1024_dec",                                   0x14e0, 0x20c;
  "mlkem1024_polyvec_compress_du",                   0x16f0, 0x03c;
  "mlkem1024_polyvec_decompress_du",                 0x1730, 0x03c;
  "mlkem1024_polyvec_tobytes",                       0x1770, 0x03c;
  "mlkem1024_polyvec_frombytes",                     0x17b0, 0x03c;
  "mlkem1024_polyvec_ntt",                           0x17f0, 0x028;
  "mlkem1024_polyvec_invntt_tomont",                 0x1820, 0x028;
  "mlkem1024_polyvec_basemul_acc_montgomery_cached", 0x1850, 0x0ac;
  "mlkem1024_polyvec_mulcache_compute",              0x1900, 0x03c;
  "mlkem1024_polyvec_reduce",                        0x1940, 0x028;
  "mlkem1024_polyvec_add",                           0x1970, 0x038;
  "mlkem1024_polyvec_tomont",                        0x19b0, 0x028;
  "mlkem1024_poly_getnoise_eta1_4x",                 0x19e0, 0x158;
  "mlkem1024_poly_getnoise_eta2",                    0x1b40, 0x0a4;
  "mlkem_poly_compress_d4",                          0x1bf0, 0x0dc;
  "mlkem_poly_compress_d10",                         0x1cd0, 0x0d4;
  "mlkem_poly_decompress_d4",                        0x1da4, 0x04c;
  "mlkem_poly_decompress_d10",                       0x1df0, 0x084;
  "mlkem_poly_compress_d5",                          0x1e74, 0x100;
  "mlkem_poly_compress_d11",                         0x1f74, 0x134;
  "mlkem_poly_decompress_d5",                        0x20b0, 0x0c0;
  "mlkem_poly_decompress_d11",                       0x2170, 0x0ec;
  "mlkem_poly_tobytes",                              0x2260, 0x03c;
  "mlkem_poly_frombytes",                            0x22a0, 0x03c;
  "mlkem_poly_frommsg",                              0x22e0, 0x05c;
  "mlkem_poly_tomsg",                                0x2340, 0x064;
  "mlk_keccak_absorb_once",                          0x23b0, 0x118;
  "mlkem_shake128_absorb_once",                      0x24d0, 0x014;
  "mlkem_shake128_squeezeblocks",                    0x24e4, 0x054;
  "mlkem_shake128_init",                             0x2540, 0x004;
  "mlkem_shake128_release",                          0x2544, 0x024;
  "mlkem_shake256",                                  0x2570, 0x0d8;
  "mlkem_sha3_256",                                  0x2650, 0x0a4;
  "mlkem_sha3_512",                                  0x26f4, 0x0a4;
  "mlk_keccak_absorb_once_x4",                       0x27a0, 0x16c;
  "mlkem_shake128x4_absorb_once",                    0x2910, 0x064;
  "mlkem_shake128x4_squeezeblocks",                  0x2974, 0x084;
  "mlkem_shake128x4_init",                           0x2a00, 0x004;
  "mlkem_shake128x4_release",                        0x2a04, 0x01c;
  "mlkem_shake256x4",                                0x2a20, 0x23c;
  "mlkem_keccakf1600_extract_bytes",                 0x2c60, 0x030;
  "mlkem_keccakf1600_xor_bytes",                     0x2c90, 0x038;
  "mlkem_keccakf1600x4_extract_bytes",               0x2cd0, 0x080;
  "mlkem_keccakf1600x4_xor_bytes",                   0x2d50, 0x080;
  "mlkem_keccakf1600_permute",                       0x2dd0, 0x5d0;
  "mlkem_keccakf1600x4_permute",                     0x33a0, 0x028;
  "mlkem512_gen_matrix",                             0x33d0, 0x0c4;
  "mlkem512_indcpa_keypair_derand",                  0x3494, 0x1f4;
  "mlkem512_indcpa_enc",                             0x3690, 0x280;
  "mlkem512_indcpa_dec",                             0x3910, 0x148;
  "mlkem512_check_pk",                               0x3a60, 0x138;
  "mlkem512_check_sk",                               0x3ba0, 0x0e8;
  "mlkem512_keypair_derand",                         0x3c90, 0x094;
  "mlkem512_keypair",                                0x3d24, 0x08c;
  "mlkem512_enc_derand",                             0x3db0, 0x0e0;
  "mlkem512_enc",                                    0x3e90, 0x098;
  "mlkem512_dec",                                    0x3f30, 0x20c;
  "mlkem_poly_tomont",                               0x4140, 0x048;
  "mlkem_poly_reduce",                               0x4190, 0x04c;
  "mlkem_poly_add",                                  0x41e0, 0x028;
  "mlkem_poly_sub",                                  0x4210, 0x028;
  "mlkem_poly_mulcache_compute",                     0x4240, 0x074;
  "mlkem_poly_ntt",                                  0x42b4, 0x0e0;
  "mlkem_poly_invntt_tomont",                        0x4394, 0x148;
  "mlkem512_polyvec_compress_du",                    0x44e0, 0x028;
  "mlkem512_polyvec_decompress_du",                  0x4510, 0x028;
  "mlkem512_polyvec_tobytes",                        0x4540, 0x028;
  "mlkem512_polyvec_frombytes",                      0x4570, 0x028;
  "mlkem512_polyvec_ntt",                            0x45a0, 0x018;
  "mlkem512_polyvec_invntt_tomont",                  0x45c0, 0x018;
  "mlkem512_polyvec_basemul_acc_montgomery_cached",  0x45e0, 0x0b4;
  "mlkem512_polyvec_mulcache_compute",               0x4694, 0x028;
  "mlkem512_polyvec_reduce",                         0x46c0, 0x018;
  "mlkem512_polyvec_add",                            0x46e0, 0x028;
  "mlkem512_polyvec_tomont",                         0x4710, 0x018;
  "mlkem512_poly_getnoise_eta1_4x",                  0x4730, 0x158;
  "mlkem512_poly_getnoise_eta2",                     0x4890, 0x0a4;
  "mlkem512_poly_getnoise_eta1122_4x",               0x4934, 0x154;
  "mlk_rej_uniform_c",                               0x4a90, 0x09c;
  "mlkem_poly_rej_uniform_x4",                       0x4b30, 0x208;
  "mlkem_poly_rej_uniform",                          0x4d40, 0x0fc;
  "mlkem_poly_cbd2",                                 0x4e40, 0x084;
  "mlkem_poly_cbd3",                                 0x4ec4, 0x08c;
  "mlkem768_gen_matrix",                             0x4f50, 0x16c;
  "mlkem768_indcpa_keypair_derand",                  0x50c0, 0x248;
  "mlkem768_indcpa_enc",                             0x5310, 0x2c8;
  "mlkem768_indcpa_dec",                             0x55e0, 0x154;
  "mlkem768_check_pk",                               0x5740, 0x138;
  "mlkem768_check_sk",                               0x5880, 0x0e8;
  "mlkem768_keypair_derand",                         0x5970, 0x094;
  "mlkem768_keypair",                                0x5a04, 0x08c;
  "mlkem768_enc_derand",                             0x5a90, 0x0e0;
  "mlkem768_enc",                                    0x5b70, 0x098;
  "mlkem768_dec",                                    0x5c10, 0x20c;
  "mlkem768_polyvec_compress_du",                    0x5e20, 0x034;
  "mlkem768_polyvec_decompress_du",                  0x5e54, 0x034;
  "mlkem768_polyvec_tobytes",                        0x5e90, 0x034;
  "mlkem768_polyvec_frombytes",                      0x5ec4, 0x034;
  "mlkem768_polyvec_ntt",                            0x5f00, 0x020;
  "mlkem768_polyvec_invntt_tomont",                  0x5f20, 0x020;
  "mlkem768_polyvec_basemul_acc_montgomery_cached",  0x5f40, 0x0ac;
  "mlkem768_polyvec_mulcache_compute",               0x5ff0, 0x034;
  "mlkem768_polyvec_reduce",                         0x6024, 0x020;
  "mlkem768_polyvec_add",                            0x6044, 0x034;
  "mlkem768_polyvec_tomont",                         0x6080, 0x020;
  "mlkem768_poly_getnoise_eta1_4x",                  0x60a0, 0x158]);;

(* ------------------------------------------------------------------------- *)
(* The read-only data, as (name, address, size): the tables with symbols,    *)
(* named after the symbol with "rodata_" in front, e.g. rodata_mlk_zetas     *)
(* (mlk_zetas is the HOL constant for its contents), and the 16-byte vectors *)
(* of constants loaded by ADRP and LDR of a Q register, which have no        *)
(* symbols. For a function f, f_consts is the block of all of the vectors    *)
(* that it loads and, if it has several, f_constK is the K-th one. The       *)
(* linker merges equal vectors, so some have several names.                  *)
(* ------------------------------------------------------------------------- *)

install_layout (layout_objects [
  "mlkem_poly_decompress_d10_consts",  0x6200, 0x010;
  "mlkem_poly_decompress_d11_consts",  0x6210, 0x010;
  "mlkem_poly_decompress_d5_consts",   0x6210, 0x010;
  "mlkem_poly_tomont_consts",          0x6220, 0x020;
  "mlkem_poly_tomont_const1",          0x6220, 0x010;
  "mlkem_poly_invntt_tomont_consts",   0x6230, 0x020;
  "mlkem_poly_invntt_tomont_const1",   0x6230, 0x010;
  "mlkem_poly_tomont_const2",          0x6230, 0x010;
  "mlkem_poly_invntt_tomont_const2",   0x6240, 0x010;
  "mlkem_poly_cbd2_consts",            0x6250, 0x040;
  "mlkem_poly_cbd2_const1",            0x6250, 0x010;
  "mlkem_poly_cbd2_const2",            0x6260, 0x010;
  "mlkem_poly_cbd2_const3",            0x6270, 0x010;
  "mlkem_poly_cbd2_const4",            0x6280, 0x010;
  "mlkem_poly_cbd3_consts",            0x6290, 0x020;
  "mlkem_poly_cbd3_const1",            0x6290, 0x010;
  "mlkem_poly_cbd3_const2",            0x62a0, 0x010;
  "rodata_mlk_KeccakF_RoundConstants", 0x62b0, 0x0c0;
  "rodata_mlk_zetas",                  0x6380, 0x100]);;

(* ------------------------------------------------------------------------- *)
(* The external symbols: the entries of the procedure linkage table for the  *)
(* functions, and the slots of the global offset table, which is not part   *)
(* of the image, for the functions and the stack guard.                      *)
(* ------------------------------------------------------------------------- *)

install_layout (layout_objects [
  "plt_memcpy",         0x0810, 0x010;
  "plt_randombytes",    0x0820, 0x010;
  "plt_stack_chk_fail", 0x0830, 0x010;
  "plt_memset",         0x0840, 0x010]);;

install_layout [
  "got_memcpy",0x1ffd0;
  "got_randombytes",0x1ffd8;
  "got_stack_chk_fail",0x1ffe0;
  "got_memset",0x1ffe8;
  "got_stack_chk_guard",0x1fff8];;

(* ------------------------------------------------------------------------- *)
(* The labels inside the functions that the proofs use, as (function,        *)
(* [label, offset from the start of the function; ...]).                     *)
(* ------------------------------------------------------------------------- *)

install_layout (layout_labels [
  "mlkem1024_check_pk",
   ["loop1",0x68; "loop1_exit",0x84];
  "mlkem1024_dec",
   ["loop1",0x120; "loop1_exit",0x13c; "loop2",0x1d8; "loop2_exit",0x204];
  "mlkem1024_polyvec_basemul_acc_montgomery_cached",
   ["loop1",0x18; "loop1_test",0xa0; "loop1_exit",0xa8; "ret",0xa8];
  "mlkem_poly_compress_d4",
   ["loop1",0x30; "loop1_test",0xac; "loop1_exit",0xb4];
  "mlkem_poly_compress_d10",
   ["loop1",0x38; "loop1_test",0xa4; "loop1_exit",0xac];
  "mlkem_poly_decompress_d4",
   ["loop1",0xc; "loop1_test",0x40; "loop1_exit",0x48];
  "mlkem_poly_decompress_d10",
   ["loop1",0x18; "loop1_test",0x78; "loop1_exit",0x80];
  "mlkem_poly_compress_d5",
   ["loop1",0x34; "loop1_test",0xd0; "loop1_exit",0xd8];
  "mlkem_poly_compress_d11",
   ["loop1",0x3c; "loop1_test",0x104; "loop1_exit",0x10c];
  "mlkem_poly_decompress_d5",
   ["loop1",0x18; "loop1_test",0xb4; "loop1_exit",0xbc];
  "mlkem_poly_decompress_d11",
   ["loop1",0x18; "loop1_test",0xe0; "loop1_exit",0xe8];
  "mlkem_poly_tobytes",
   ["loop1",0x8; "loop1_test",0x30; "loop1_exit",0x38; "ret",0x38];
  "mlkem_poly_frombytes",
   ["loop1",0x8; "loop1_test",0x30; "loop1_exit",0x38];
  "mlkem_poly_frommsg",
   ["loop1",0x18; "loop1_test",0x50; "loop1_exit",0x58];
  "mlkem_poly_tomsg",
   ["loop1",0x18; "loop1_test",0x58; "loop1_exit",0x60];
  "mlk_keccak_absorb_once",
   ["loop1",0x50; "loop1_test",0x74; "loop1_exit",0x7c];
  "mlkem_shake128_squeezeblocks",
   ["loop1",0x1c; "loop1_exit",0x44];
  "mlkem_shake256",
   ["after_mlk_keccak_absorb_once",0x40; "loop1",0x50; "loop1_exit",0x80];
  "mlk_keccak_absorb_once_x4",
   ["loop1",0x58; "loop1_test",0x94; "loop1_exit",0x9c];
  "mlkem_shake128x4_squeezeblocks",
   ["loop1",0x2c; "loop1_exit",0x6c];
  "mlkem_shake256x4",
   ["after_mlk_keccak_absorb_once_x4",0x98; "loop1",0xa8; "loop1_exit",0xdc;
    "join2",0x108];
  "mlkem_keccakf1600_extract_bytes",
   ["loop1",0x18; "loop1_test",0x24; "loop1_exit",0x2c];
  "mlkem_keccakf1600_xor_bytes",
   ["loop1",0x18; "loop1_test",0x2c; "loop1_exit",0x34];
  "mlkem_keccakf1600_permute",
   ["adrp1",0x4; "loop1",0xb0; "loop1_back",0x558; "loop1_exit",0x55c];
  "mlkem512_check_pk",
   ["loop1",0x68; "loop1_exit",0x84];
  "mlkem512_dec",
   ["loop1",0x120; "loop1_exit",0x13c; "loop2",0x1d8; "loop2_exit",0x204];
  "mlkem_poly_tomont",
   ["loop1",0x18; "loop1_test",0x3c; "loop1_exit",0x44; "ret",0x44];
  "mlkem_poly_reduce",
   ["loop1",0x10; "loop1_test",0x40; "loop1_exit",0x48; "ret",0x48];
  "mlkem_poly_add",
   ["loop1",0x8; "loop1_test",0x1c; "loop1_exit",0x24];
  "mlkem_poly_sub",
   ["loop1",0x8; "loop1_test",0x1c; "loop1_exit",0x24];
  "mlkem_poly_mulcache_compute",
   ["loop1",0x20; "loop1_test",0x68; "loop1_exit",0x70; "ret",0x70];
  "mlkem_poly_ntt",
   ["loop1",0x2c; "loop2",0x44; "loop3",0x74; "loop3_test",0xa4;
    "loop3_exit",0xac; "loop2_test",0xb4; "loop2_next",0xbc;
    "loop2_exit",0xc4; "ret",0xdc];
  "mlkem_poly_invntt_tomont",
   ["adrp1",0x4; "adrp2",0x14; "loop1",0x24; "loop1_test",0x48; "adrp3",0x50;
    "loop1_exit",0x50; "loop2",0x7c; "loop3",0x94; "loop4",0xc4;
    "loop4_test",0x108; "loop4_exit",0x110; "loop3_test",0x118;
    "loop3_next",0x120; "loop3_exit",0x128; "loop2_exit",0x140];
  "mlkem512_polyvec_basemul_acc_montgomery_cached",
   ["loop1",0x20; "loop1_test",0xa8; "loop1_exit",0xb0; "ret",0xb0];
  "mlk_rej_uniform_c",
   ["loop1",0x54; "loop1_exit",0x98; "ret",0x98];
  "mlkem_poly_rej_uniform_x4",
   ["after_mlk_rej_uniform_c_4",0xf4; "loop1",0x120; "loop1_exit",0x1b0];
  "mlkem_poly_rej_uniform",
   ["after_mlk_rej_uniform_c_1",0x74; "loop1",0x80; "loop1_exit",0xb0];
  "mlkem_poly_cbd2",
   ["loop1",0x30; "loop1_test",0x78; "loop1_exit",0x80];
  "mlkem_poly_cbd3",
   ["loop1",0x2c; "loop1_test",0x80; "loop1_exit",0x88];
  "mlkem768_check_pk",
   ["loop1",0x68; "loop1_exit",0x84];
  "mlkem768_dec",
   ["loop1",0x120; "loop1_exit",0x13c; "loop2",0x1d8; "loop2_exit",0x204];
  "mlkem768_polyvec_basemul_acc_montgomery_cached",
   ["loop1",0x18; "loop1_test",0xa0; "loop1_exit",0xa8; "ret",0xa8]]);;

(* ------------------------------------------------------------------------- *)
(* The separately transcribed functions, as (name, function), where the     *)
(* name is that of the transcription without the prefix and suffix.         *)
(* ------------------------------------------------------------------------- *)

install_layout (layout_copies [
  "basemul_k2",
   "mlkem512_polyvec_basemul_acc_montgomery_cached";
  "basemul_k3",
   "mlkem768_polyvec_basemul_acc_montgomery_cached";
  "basemul_k4",
   "mlkem1024_polyvec_basemul_acc_montgomery_cached";
  "keccakf1600_permute",
   "mlkem_keccakf1600_permute";
  "poly_invntt_tomont",
   "mlkem_poly_invntt_tomont";
  "poly_mulcache_compute",
   "mlkem_poly_mulcache_compute";
  "poly_ntt",
   "mlkem_poly_ntt";
  "poly_reduce",
   "mlkem_poly_reduce";
  "poly_tobytes",
   "mlkem_poly_tobytes";
  "poly_tomont",
   "mlkem_poly_tomont";
  "rej_uniform",
   "mlk_rej_uniform_c"]);;
