(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA-256 block compression, Intel SHA extensions (SHA-NI) x86 version.     *)
(*                                                                           *)
(* The code is emitted by the Ragamuffin transpiler; it computes the FIPS    *)
(* 180-4 SHA-256 compression function over num_blocks 64-byte big-endian     *)
(* message blocks, updating the 8-word state in place, using the Intel SHA   *)
(* extensions (SHA256RNDS2 / SHA256MSG1 / SHA256MSG2) plus the SSE repack     *)
(* ops (PSHUFD / PALIGNR / PUNPCKLQDQ / PUNPCKHQDQ / PADDD / PSHUFB):         *)
(*                                                                           *)
(* extern void sha256_compress_hw                                            *)
(*   (uint32_t state[static 8], const uint8_t *data, size_t num_blocks);     *)
(*                                                                           *)
(* SysV: RDI = state, RSI = data, RDX = num_blocks (must be nonzero).        *)
(* Win64: RCX = state, RDX = data, R8 = num_blocks; the shim copies these    *)
(* into the SysV registers and (unlike SysV) saves the callee-saved xmm6-10. *)
(*                                                                           *)
(* Unlike the scalar nohw routine, this code has NO stack frame on SysV, no  *)
(* scratch memory and no callee-saved GPR pushes: a single do-while          *)
(* (dec rdx; jnz) block loop with the 64 rounds fully unrolled across the    *)
(* xmm registers.                                                            *)
(*                                                                           *)
(* The K256 round-constant table lives in .rodata and is addressed           *)
(* RIP-relatively (lea K256+128(%rip),%rcx), so the code is frozen with      *)
(* define_assert_relocs_from_elf. K256 is 608 bytes:                         *)
(*                                                                           *)
(*   +0   .. +511 : the 64 round constants K[0..63], each 16-byte row        *)
(*                  DOUBLED (so K[4i..4i+3] occupies bytes 32i..32i+15 and    *)
(*                  again 32i+16..32i+31); 2*16*16 = 512 bytes.              *)
(*   +512 .. +527 : big-endian byteswap mask 0x00010203,04050607,           *)
(*                  08090a0b,0c0d0e0f (loaded into xmm7 via                   *)
(*                  movdqa [rcx+512-128], rcx = K256+128, for the pshufb      *)
(*                  message byteswap), then doubled at +528.                  *)
(*   +544 .. +575 : 0x03020100,0b0a0908,ffffffff,ffffffff (doubled) -- the    *)
(*                  low/high half-blend masks from the original OpenSSL       *)
(*                  layout; not referenced by this routine.                   *)
(*   +576 .. +607 : ffffffff,ffffffff,03020100,0b0a0908 (doubled) -- ditto.   *)
(*                                                                           *)
(* Because rcx = K256+128, the round-constant loads use displacements        *)
(* rcx-128 .. rcx+352 (= K256+0 .. K256+480), i.e. movdqa [rcx+32k-128]      *)
(* selects the doubled row for rounds 4k..4k+3.                              *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/consttime.ml";;
needs "x86/proofs/utils/sha256_spec.ml";;
needs "x86/proofs/utils/sha256_bridge.ml";;

(* ------------------------------------------------------------------------- *)
(* FROZEN MACHINE CODE (Phase 0 freeze, Phase 1 wired).                      *)
(*                                                                           *)
(* The byte-list definitions below are the frozen machine code with the      *)
(* K256 table relocation abstracted, one per ABI, wired into a live          *)
(* define_assert_relocs_from_elf (Phase 1: the SHA-NI opcodes 0F 38 CB/CC/CD,*)
(* 66 0F 3A 0F, 66 0F 6C/6D are now in the s2n-bignum x86 ISA model, so the   *)
(* decoder handles them; cold-gated S027_PHASE1_COLD_PASS, axioms=3). The     *)
(* byte streams were generated from the assembled objects (see               *)
(* orchestrator/logs/gen_hw_skeleton.py, cross-checked byte-for-byte against  *)
(* the .text size); define_assert_relocs_from_elf re-derives them from the    *)
(* object itself and asserts they match.                                     *)
(*                                                                           *)
(*   - SysV    (x86/sha256/sha256_compress_hw.o):  .text 825 B, one          *)
(*     R_X86_64_PC32 reloc at .text+0x7 -> K256 (ELF addend 0x7c); the ADDR   *)
(*     marker names "K256" (WHOLE_READONLY blob), duplicate -> unused_.       *)
(*   - Windows (x86/sha256/sha256_compress_hw.obj): .text 900 B, reloc at     *)
(*     .text+0x31 (same addend); +75 vs SysV = the endbr64 shim (push rdi/rsi,*)
(*     mov args) + xmm6-10 save/restore in the WINDOWS_ABI region (sub/add    *)
(*     rsp,80 + 5+5 movups via CFI_STACKSAVEU/LOADU, human fix d5989555). The  *)
(*     ADDR marker MUST name "K256W" (not "K256") to avoid clashing with the  *)
(*     already-defined SysV K256 byte-list, else assert_relocs mismatches at  *)
(*     pc 0x31 (mirrors nohw's K256/K256W split).                            *)
(* ------------------------------------------------------------------------- *)

(* ----- SysV mc/tmc/EXEC (x86/sha256/sha256_compress_hw.o) ----------------- *)
(* Phase 1: the SHA-NI + SSE decode clauses now exist, so the live            *)
(* define_assert_relocs_from_elf decodes every instruction.  WHOLE_READONLY   *)
(* -> "K256" (the 608-byte rodata blob); the per-symbol duplicate -> unused_. *)

let sha256_compress_hw_mc,rodata_constants_data =
  define_assert_relocs_from_elf
    ~map_symbol_name:(function "WHOLE_READONLY" -> "K256"
                             | s -> "unused_" ^ s)
    "sha256_compress_hw_mc"
    "x86/sha256/sha256_compress_hw.o"
(fun b ADDR -> [b[
  0xf3; 0x0f; 0x1e; 0xfa;  (* endbr64 *)
  0x48; 0x8d; 0x0d]; ADDR ("K256",(124)); b[
                           (* lea rcx,[rip+0x0] *)
  0xf3; 0x0f; 0x6f; 0x0f;  (* movdqu xmm1,XMMWORD PTR [rdi] *)
  0xf3; 0x0f; 0x6f; 0x57; 0x10; (* movdqu xmm2,XMMWORD PTR [rdi+0x10] *)
  0x66; 0x0f; 0x6f; 0xb9; 0x80; 0x01; 0x00; 0x00; (* movdqa xmm7,XMMWORD PTR [rcx+0x180] *)
  0x66; 0x0f; 0x70; 0xc1; 0x1b; (* pshufd xmm0,xmm1,0x1b *)
  0x66; 0x0f; 0x70; 0xc9; 0xb1; (* pshufd xmm1,xmm1,0xb1 *)
  0x66; 0x0f; 0x70; 0xd2; 0x1b; (* pshufd xmm2,xmm2,0x1b *)
  0x66; 0x44; 0x0f; 0x6f; 0xc7; (* movdqa xmm8,xmm7 *)
  0x66; 0x0f; 0x3a; 0x0f; 0xca; 0x08; (* palignr xmm1,xmm2,0x8 *)
  0x66; 0x0f; 0x6c; 0xd0;  (* punpcklqdq xmm2,xmm0 *)
  0xeb; 0x00;              (* jmp 3c <Lsha256_compress_hw_oop_shaext> *)
  0xf3; 0x0f; 0x6f; 0x1e;  (* movdqu xmm3,XMMWORD PTR [rsi] *)
  0xf3; 0x0f; 0x6f; 0x66; 0x10; (* movdqu xmm4,XMMWORD PTR [rsi+0x10] *)
  0xf3; 0x0f; 0x6f; 0x6e; 0x20; (* movdqu xmm5,XMMWORD PTR [rsi+0x20] *)
  0x66; 0x0f; 0x38; 0x00; 0xdf; (* pshufb xmm3,xmm7 *)
  0xf3; 0x0f; 0x6f; 0x76; 0x30; (* movdqu xmm6,XMMWORD PTR [rsi+0x30] *)
  0x66; 0x0f; 0x6f; 0x41; 0x80; (* movdqa xmm0,XMMWORD PTR [rcx-0x80] *)
  0x66; 0x0f; 0xfe; 0xc3;  (* paddd xmm0,xmm3 *)
  0x66; 0x0f; 0x38; 0x00; 0xe7; (* pshufb xmm4,xmm7 *)
  0x66; 0x44; 0x0f; 0x6f; 0xd2; (* movdqa xmm10,xmm2 *)
  0x0f; 0x38; 0xcb; 0xd1;  (* sha256rnds2 xmm2,xmm1,xmm0 *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e; (* pshufd xmm0,xmm0,0xe *)
  0x90;                    (* nop *)
  0x66; 0x44; 0x0f; 0x6f; 0xc9; (* movdqa xmm9,xmm1 *)
  0x0f; 0x38; 0xcb; 0xca;  (* sha256rnds2 xmm1,xmm2,xmm0 *)
  0x66; 0x0f; 0x6f; 0x41; 0xa0; (* movdqa xmm0,XMMWORD PTR [rcx-0x60] *)
  0x66; 0x0f; 0xfe; 0xc4;  (* paddd xmm0,xmm4 *)
  0x66; 0x0f; 0x38; 0x00; 0xef; (* pshufb xmm5,xmm7 *)
  0x0f; 0x38; 0xcb; 0xd1;  (* sha256rnds2 xmm2,xmm1,xmm0 *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e; (* pshufd xmm0,xmm0,0xe *)
  0x48; 0x8d; 0x76; 0x40;  (* lea rsi,[rsi+0x40] *)
  0x0f; 0x38; 0xcc; 0xdc;  (* sha256msg1 xmm3,xmm4 *)
  0x0f; 0x38; 0xcb; 0xca;  (* sha256rnds2 xmm1,xmm2,xmm0 *)
  0x66; 0x0f; 0x6f; 0x41; 0xc0; (* movdqa xmm0,XMMWORD PTR [rcx-0x40] *)
  0x66; 0x0f; 0xfe; 0xc5;  (* paddd xmm0,xmm5 *)
  0x66; 0x0f; 0x38; 0x00; 0xf7; (* pshufb xmm6,xmm7 *)
  0x0f; 0x38; 0xcb; 0xd1;  (* sha256rnds2 xmm2,xmm1,xmm0 *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e; (* pshufd xmm0,xmm0,0xe *)
  0x66; 0x0f; 0x6f; 0xfe;  (* movdqa xmm7,xmm6 *)
  0x66; 0x0f; 0x3a; 0x0f; 0xfd; 0x04; (* palignr xmm7,xmm5,0x4 *)
  0x90;                    (* nop *)
  0x66; 0x0f; 0xfe; 0xdf;  (* paddd xmm3,xmm7 *)
  0x0f; 0x38; 0xcc; 0xe5;  (* sha256msg1 xmm4,xmm5 *)
  0x0f; 0x38; 0xcb; 0xca;  (* sha256rnds2 xmm1,xmm2,xmm0 *)
  0x66; 0x0f; 0x6f; 0x41; 0xe0; (* movdqa xmm0,XMMWORD PTR [rcx-0x20] *)
  0x66; 0x0f; 0xfe; 0xc6;  (* paddd xmm0,xmm6 *)
  0x0f; 0x38; 0xcd; 0xde;  (* sha256msg2 xmm3,xmm6 *)
  0x0f; 0x38; 0xcb; 0xd1;  (* sha256rnds2 xmm2,xmm1,xmm0 *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e; (* pshufd xmm0,xmm0,0xe *)
  0x66; 0x0f; 0x6f; 0xfb;  (* movdqa xmm7,xmm3 *)
  0x66; 0x0f; 0x3a; 0x0f; 0xfe; 0x04; (* palignr xmm7,xmm6,0x4 *)
  0x90;                    (* nop *)
  0x66; 0x0f; 0xfe; 0xe7;  (* paddd xmm4,xmm7 *)
  0x0f; 0x38; 0xcc; 0xee;  (* sha256msg1 xmm5,xmm6 *)
  0x0f; 0x38; 0xcb; 0xca;  (* sha256rnds2 xmm1,xmm2,xmm0 *)
  0x66; 0x0f; 0x6f; 0x01;  (* movdqa xmm0,XMMWORD PTR [rcx] *)
  0x66; 0x0f; 0xfe; 0xc3;  (* paddd xmm0,xmm3 *)
  0x0f; 0x38; 0xcd; 0xe3;  (* sha256msg2 xmm4,xmm3 *)
  0x0f; 0x38; 0xcb; 0xd1;  (* sha256rnds2 xmm2,xmm1,xmm0 *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e; (* pshufd xmm0,xmm0,0xe *)
  0x66; 0x0f; 0x6f; 0xfc;  (* movdqa xmm7,xmm4 *)
  0x66; 0x0f; 0x3a; 0x0f; 0xfb; 0x04; (* palignr xmm7,xmm3,0x4 *)
  0x90;                    (* nop *)
  0x66; 0x0f; 0xfe; 0xef;  (* paddd xmm5,xmm7 *)
  0x0f; 0x38; 0xcc; 0xf3;  (* sha256msg1 xmm6,xmm3 *)
  0x0f; 0x38; 0xcb; 0xca;  (* sha256rnds2 xmm1,xmm2,xmm0 *)
  0x66; 0x0f; 0x6f; 0x41; 0x20; (* movdqa xmm0,XMMWORD PTR [rcx+0x20] *)
  0x66; 0x0f; 0xfe; 0xc4;  (* paddd xmm0,xmm4 *)
  0x0f; 0x38; 0xcd; 0xec;  (* sha256msg2 xmm5,xmm4 *)
  0x0f; 0x38; 0xcb; 0xd1;  (* sha256rnds2 xmm2,xmm1,xmm0 *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e; (* pshufd xmm0,xmm0,0xe *)
  0x66; 0x0f; 0x6f; 0xfd;  (* movdqa xmm7,xmm5 *)
  0x66; 0x0f; 0x3a; 0x0f; 0xfc; 0x04; (* palignr xmm7,xmm4,0x4 *)
  0x90;                    (* nop *)
  0x66; 0x0f; 0xfe; 0xf7;  (* paddd xmm6,xmm7 *)
  0x0f; 0x38; 0xcc; 0xdc;  (* sha256msg1 xmm3,xmm4 *)
  0x0f; 0x38; 0xcb; 0xca;  (* sha256rnds2 xmm1,xmm2,xmm0 *)
  0x66; 0x0f; 0x6f; 0x41; 0x40; (* movdqa xmm0,XMMWORD PTR [rcx+0x40] *)
  0x66; 0x0f; 0xfe; 0xc5;  (* paddd xmm0,xmm5 *)
  0x0f; 0x38; 0xcd; 0xf5;  (* sha256msg2 xmm6,xmm5 *)
  0x0f; 0x38; 0xcb; 0xd1;  (* sha256rnds2 xmm2,xmm1,xmm0 *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e; (* pshufd xmm0,xmm0,0xe *)
  0x66; 0x0f; 0x6f; 0xfe;  (* movdqa xmm7,xmm6 *)
  0x66; 0x0f; 0x3a; 0x0f; 0xfd; 0x04; (* palignr xmm7,xmm5,0x4 *)
  0x90;                    (* nop *)
  0x66; 0x0f; 0xfe; 0xdf;  (* paddd xmm3,xmm7 *)
  0x0f; 0x38; 0xcc; 0xe5;  (* sha256msg1 xmm4,xmm5 *)
  0x0f; 0x38; 0xcb; 0xca;  (* sha256rnds2 xmm1,xmm2,xmm0 *)
  0x66; 0x0f; 0x6f; 0x41; 0x60; (* movdqa xmm0,XMMWORD PTR [rcx+0x60] *)
  0x66; 0x0f; 0xfe; 0xc6;  (* paddd xmm0,xmm6 *)
  0x0f; 0x38; 0xcd; 0xde;  (* sha256msg2 xmm3,xmm6 *)
  0x0f; 0x38; 0xcb; 0xd1;  (* sha256rnds2 xmm2,xmm1,xmm0 *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e; (* pshufd xmm0,xmm0,0xe *)
  0x66; 0x0f; 0x6f; 0xfb;  (* movdqa xmm7,xmm3 *)
  0x66; 0x0f; 0x3a; 0x0f; 0xfe; 0x04; (* palignr xmm7,xmm6,0x4 *)
  0x90;                    (* nop *)
  0x66; 0x0f; 0xfe; 0xe7;  (* paddd xmm4,xmm7 *)
  0x0f; 0x38; 0xcc; 0xee;  (* sha256msg1 xmm5,xmm6 *)
  0x0f; 0x38; 0xcb; 0xca;  (* sha256rnds2 xmm1,xmm2,xmm0 *)
  0x66; 0x0f; 0x6f; 0x81; 0x80; 0x00; 0x00; 0x00; (* movdqa xmm0,XMMWORD PTR [rcx+0x80] *)
  0x66; 0x0f; 0xfe; 0xc3;  (* paddd xmm0,xmm3 *)
  0x0f; 0x38; 0xcd; 0xe3;  (* sha256msg2 xmm4,xmm3 *)
  0x0f; 0x38; 0xcb; 0xd1;  (* sha256rnds2 xmm2,xmm1,xmm0 *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e; (* pshufd xmm0,xmm0,0xe *)
  0x66; 0x0f; 0x6f; 0xfc;  (* movdqa xmm7,xmm4 *)
  0x66; 0x0f; 0x3a; 0x0f; 0xfb; 0x04; (* palignr xmm7,xmm3,0x4 *)
  0x90;                    (* nop *)
  0x66; 0x0f; 0xfe; 0xef;  (* paddd xmm5,xmm7 *)
  0x0f; 0x38; 0xcc; 0xf3;  (* sha256msg1 xmm6,xmm3 *)
  0x0f; 0x38; 0xcb; 0xca;  (* sha256rnds2 xmm1,xmm2,xmm0 *)
  0x66; 0x0f; 0x6f; 0x81; 0xa0; 0x00; 0x00; 0x00; (* movdqa xmm0,XMMWORD PTR [rcx+0xa0] *)
  0x66; 0x0f; 0xfe; 0xc4;  (* paddd xmm0,xmm4 *)
  0x0f; 0x38; 0xcd; 0xec;  (* sha256msg2 xmm5,xmm4 *)
  0x0f; 0x38; 0xcb; 0xd1;  (* sha256rnds2 xmm2,xmm1,xmm0 *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e; (* pshufd xmm0,xmm0,0xe *)
  0x66; 0x0f; 0x6f; 0xfd;  (* movdqa xmm7,xmm5 *)
  0x66; 0x0f; 0x3a; 0x0f; 0xfc; 0x04; (* palignr xmm7,xmm4,0x4 *)
  0x90;                    (* nop *)
  0x66; 0x0f; 0xfe; 0xf7;  (* paddd xmm6,xmm7 *)
  0x0f; 0x38; 0xcc; 0xdc;  (* sha256msg1 xmm3,xmm4 *)
  0x0f; 0x38; 0xcb; 0xca;  (* sha256rnds2 xmm1,xmm2,xmm0 *)
  0x66; 0x0f; 0x6f; 0x81; 0xc0; 0x00; 0x00; 0x00; (* movdqa xmm0,XMMWORD PTR [rcx+0xc0] *)
  0x66; 0x0f; 0xfe; 0xc5;  (* paddd xmm0,xmm5 *)
  0x0f; 0x38; 0xcd; 0xf5;  (* sha256msg2 xmm6,xmm5 *)
  0x0f; 0x38; 0xcb; 0xd1;  (* sha256rnds2 xmm2,xmm1,xmm0 *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e; (* pshufd xmm0,xmm0,0xe *)
  0x66; 0x0f; 0x6f; 0xfe;  (* movdqa xmm7,xmm6 *)
  0x66; 0x0f; 0x3a; 0x0f; 0xfd; 0x04; (* palignr xmm7,xmm5,0x4 *)
  0x90;                    (* nop *)
  0x66; 0x0f; 0xfe; 0xdf;  (* paddd xmm3,xmm7 *)
  0x0f; 0x38; 0xcc; 0xe5;  (* sha256msg1 xmm4,xmm5 *)
  0x0f; 0x38; 0xcb; 0xca;  (* sha256rnds2 xmm1,xmm2,xmm0 *)
  0x66; 0x0f; 0x6f; 0x81; 0xe0; 0x00; 0x00; 0x00; (* movdqa xmm0,XMMWORD PTR [rcx+0xe0] *)
  0x66; 0x0f; 0xfe; 0xc6;  (* paddd xmm0,xmm6 *)
  0x0f; 0x38; 0xcd; 0xde;  (* sha256msg2 xmm3,xmm6 *)
  0x0f; 0x38; 0xcb; 0xd1;  (* sha256rnds2 xmm2,xmm1,xmm0 *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e; (* pshufd xmm0,xmm0,0xe *)
  0x66; 0x0f; 0x6f; 0xfb;  (* movdqa xmm7,xmm3 *)
  0x66; 0x0f; 0x3a; 0x0f; 0xfe; 0x04; (* palignr xmm7,xmm6,0x4 *)
  0x90;                    (* nop *)
  0x66; 0x0f; 0xfe; 0xe7;  (* paddd xmm4,xmm7 *)
  0x0f; 0x38; 0xcc; 0xee;  (* sha256msg1 xmm5,xmm6 *)
  0x0f; 0x38; 0xcb; 0xca;  (* sha256rnds2 xmm1,xmm2,xmm0 *)
  0x66; 0x0f; 0x6f; 0x81; 0x00; 0x01; 0x00; 0x00; (* movdqa xmm0,XMMWORD PTR [rcx+0x100] *)
  0x66; 0x0f; 0xfe; 0xc3;  (* paddd xmm0,xmm3 *)
  0x0f; 0x38; 0xcd; 0xe3;  (* sha256msg2 xmm4,xmm3 *)
  0x0f; 0x38; 0xcb; 0xd1;  (* sha256rnds2 xmm2,xmm1,xmm0 *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e; (* pshufd xmm0,xmm0,0xe *)
  0x66; 0x0f; 0x6f; 0xfc;  (* movdqa xmm7,xmm4 *)
  0x66; 0x0f; 0x3a; 0x0f; 0xfb; 0x04; (* palignr xmm7,xmm3,0x4 *)
  0x90;                    (* nop *)
  0x66; 0x0f; 0xfe; 0xef;  (* paddd xmm5,xmm7 *)
  0x0f; 0x38; 0xcc; 0xf3;  (* sha256msg1 xmm6,xmm3 *)
  0x0f; 0x38; 0xcb; 0xca;  (* sha256rnds2 xmm1,xmm2,xmm0 *)
  0x66; 0x0f; 0x6f; 0x81; 0x20; 0x01; 0x00; 0x00; (* movdqa xmm0,XMMWORD PTR [rcx+0x120] *)
  0x66; 0x0f; 0xfe; 0xc4;  (* paddd xmm0,xmm4 *)
  0x0f; 0x38; 0xcd; 0xec;  (* sha256msg2 xmm5,xmm4 *)
  0x0f; 0x38; 0xcb; 0xd1;  (* sha256rnds2 xmm2,xmm1,xmm0 *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e; (* pshufd xmm0,xmm0,0xe *)
  0x66; 0x0f; 0x6f; 0xfd;  (* movdqa xmm7,xmm5 *)
  0x66; 0x0f; 0x3a; 0x0f; 0xfc; 0x04; (* palignr xmm7,xmm4,0x4 *)
  0x0f; 0x38; 0xcb; 0xca;  (* sha256rnds2 xmm1,xmm2,xmm0 *)
  0x66; 0x0f; 0xfe; 0xf7;  (* paddd xmm6,xmm7 *)
  0x66; 0x0f; 0x6f; 0x81; 0x40; 0x01; 0x00; 0x00; (* movdqa xmm0,XMMWORD PTR [rcx+0x140] *)
  0x66; 0x0f; 0xfe; 0xc5;  (* paddd xmm0,xmm5 *)
  0x0f; 0x38; 0xcb; 0xd1;  (* sha256rnds2 xmm2,xmm1,xmm0 *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e; (* pshufd xmm0,xmm0,0xe *)
  0x0f; 0x38; 0xcd; 0xf5;  (* sha256msg2 xmm6,xmm5 *)
  0x66; 0x41; 0x0f; 0x6f; 0xf8; (* movdqa xmm7,xmm8 *)
  0x0f; 0x38; 0xcb; 0xca;  (* sha256rnds2 xmm1,xmm2,xmm0 *)
  0x66; 0x0f; 0x6f; 0x81; 0x60; 0x01; 0x00; 0x00; (* movdqa xmm0,XMMWORD PTR [rcx+0x160] *)
  0x66; 0x0f; 0xfe; 0xc6;  (* paddd xmm0,xmm6 *)
  0x90;                    (* nop *)
  0x0f; 0x38; 0xcb; 0xd1;  (* sha256rnds2 xmm2,xmm1,xmm0 *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e; (* pshufd xmm0,xmm0,0xe *)
  0x48; 0xff; 0xca;        (* dec rdx *)
  0x90;                    (* nop *)
  0x0f; 0x38; 0xcb; 0xca;  (* sha256rnds2 xmm1,xmm2,xmm0 *)
  0x66; 0x41; 0x0f; 0xfe; 0xd2; (* paddd xmm2,xmm10 *)
  0x66; 0x41; 0x0f; 0xfe; 0xc9; (* paddd xmm1,xmm9 *)
  0x0f; 0x85; 0x26; 0xfd; 0xff; 0xff; (* jne 3c <Lsha256_compress_hw_oop_shaext> *)
  0x66; 0x0f; 0x70; 0xd2; 0xb1; (* pshufd xmm2,xmm2,0xb1 *)
  0x66; 0x0f; 0x70; 0xf9; 0x1b; (* pshufd xmm7,xmm1,0x1b *)
  0x66; 0x0f; 0x70; 0xc9; 0xb1; (* pshufd xmm1,xmm1,0xb1 *)
  0x66; 0x0f; 0x6d; 0xca;  (* punpckhqdq xmm1,xmm2 *)
  0x66; 0x0f; 0x3a; 0x0f; 0xd7; 0x08; (* palignr xmm2,xmm7,0x8 *)
  0xf3; 0x0f; 0x7f; 0x0f;  (* movdqu XMMWORD PTR [rdi],xmm1 *)
  0xf3; 0x0f; 0x7f; 0x57; 0x10; (* movdqu XMMWORD PTR [rdi+0x10],xmm2 *)
  0xc3;                    (* ret *)
]]);;

(* The byte-list definition of the K256 table: |- K256 = [...] (608 bytes). *)
let K256_DATA =
  List.find (fun th -> name_of(lhs(concl th)) = "K256") rodata_constants_data;;

let sha256_compress_hw_tmc =
  define_trimmed "sha256_compress_hw_tmc" sha256_compress_hw_mc;;

(* X86_MK_EXEC_RULE (not the CORE variant): the reloc-parameterized mc's       *)
(* BUTLAST step in X86_TRIM_EXEC_RULE fails (AP_TERM) when the mc is           *)
(* quantified over pc and rodata symbols (nohw + curve25519_x25519base). *)
let SHA256_COMPRESS_HW_EXEC =
  X86_MK_EXEC_RULE sha256_compress_hw_tmc;;

(* ----- Windows mc/tmc/EXEC (x86/sha256/sha256_compress_hw.obj) ------------- *)
(* WHOLE_READONLY -> "K256W" (NOT "K256") to avoid clashing with the already-  *)
(* defined SysV K256 byte-list; per-symbol duplicate -> unusedW_.             *)

let sha256_compress_hw_windows_mc,rodata_constants_data_w =
  define_assert_relocs_from_elf
    ~map_symbol_name:(function "WHOLE_READONLY" -> "K256W"
                             | s -> "unusedW_" ^ s)
    "sha256_compress_hw_windows_mc"
    "x86/sha256/sha256_compress_hw.obj"
(fun b ADDR -> [b[
  0xf3; 0x0f; 0x1e; 0xfa;  (* endbr64 *)
  0x57;                    (* push rdi *)
  0x56;                    (* push rsi *)
  0x48; 0x89; 0xcf;        (* mov rdi,rcx *)
  0x48; 0x89; 0xd6;        (* mov rsi,rdx *)
  0x4c; 0x89; 0xc2;        (* mov rdx,r8 *)
  0x48; 0x83; 0xec; 0x50;  (* sub rsp,0x50 *)
  0x0f; 0x11; 0x34; 0x24;  (* movups XMMWORD PTR [rsp],xmm6 *)
  0x0f; 0x11; 0x7c; 0x24; 0x10; (* movups XMMWORD PTR [rsp+0x10],xmm7 *)
  0x44; 0x0f; 0x11; 0x44; 0x24; 0x20; (* movups XMMWORD PTR [rsp+0x20],xmm8 *)
  0x44; 0x0f; 0x11; 0x4c; 0x24; 0x30; (* movups XMMWORD PTR [rsp+0x30],xmm9 *)
  0x44; 0x0f; 0x11; 0x54; 0x24; 0x40; (* movups XMMWORD PTR [rsp+0x40],xmm10 *)
  0x48; 0x8d; 0x0d]; ADDR ("K256W",(124)); b[
                           (* lea rcx,[rip+0x0] *)
  0xf3; 0x0f; 0x6f; 0x0f;  (* movdqu xmm1,XMMWORD PTR [rdi] *)
  0xf3; 0x0f; 0x6f; 0x57; 0x10; (* movdqu xmm2,XMMWORD PTR [rdi+0x10] *)
  0x66; 0x0f; 0x6f; 0xb9; 0x80; 0x01; 0x00; 0x00; (* movdqa xmm7,XMMWORD PTR [rcx+0x180] *)
  0x66; 0x0f; 0x70; 0xc1; 0x1b; (* pshufd xmm0,xmm1,0x1b *)
  0x66; 0x0f; 0x70; 0xc9; 0xb1; (* pshufd xmm1,xmm1,0xb1 *)
  0x66; 0x0f; 0x70; 0xd2; 0x1b; (* pshufd xmm2,xmm2,0x1b *)
  0x66; 0x44; 0x0f; 0x6f; 0xc7; (* movdqa xmm8,xmm7 *)
  0x66; 0x0f; 0x3a; 0x0f; 0xca; 0x08; (* palignr xmm1,xmm2,0x8 *)
  0x66; 0x0f; 0x6c; 0xd0;  (* punpcklqdq xmm2,xmm0 *)
  0xeb; 0x00;              (* jmp 66 <Lsha256_compress_hw_oop_shaext> *)
  0xf3; 0x0f; 0x6f; 0x1e;  (* movdqu xmm3,XMMWORD PTR [rsi] *)
  0xf3; 0x0f; 0x6f; 0x66; 0x10; (* movdqu xmm4,XMMWORD PTR [rsi+0x10] *)
  0xf3; 0x0f; 0x6f; 0x6e; 0x20; (* movdqu xmm5,XMMWORD PTR [rsi+0x20] *)
  0x66; 0x0f; 0x38; 0x00; 0xdf; (* pshufb xmm3,xmm7 *)
  0xf3; 0x0f; 0x6f; 0x76; 0x30; (* movdqu xmm6,XMMWORD PTR [rsi+0x30] *)
  0x66; 0x0f; 0x6f; 0x41; 0x80; (* movdqa xmm0,XMMWORD PTR [rcx-0x80] *)
  0x66; 0x0f; 0xfe; 0xc3;  (* paddd xmm0,xmm3 *)
  0x66; 0x0f; 0x38; 0x00; 0xe7; (* pshufb xmm4,xmm7 *)
  0x66; 0x44; 0x0f; 0x6f; 0xd2; (* movdqa xmm10,xmm2 *)
  0x0f; 0x38; 0xcb; 0xd1;  (* sha256rnds2 xmm2,xmm1,xmm0 *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e; (* pshufd xmm0,xmm0,0xe *)
  0x90;                    (* nop *)
  0x66; 0x44; 0x0f; 0x6f; 0xc9; (* movdqa xmm9,xmm1 *)
  0x0f; 0x38; 0xcb; 0xca;  (* sha256rnds2 xmm1,xmm2,xmm0 *)
  0x66; 0x0f; 0x6f; 0x41; 0xa0; (* movdqa xmm0,XMMWORD PTR [rcx-0x60] *)
  0x66; 0x0f; 0xfe; 0xc4;  (* paddd xmm0,xmm4 *)
  0x66; 0x0f; 0x38; 0x00; 0xef; (* pshufb xmm5,xmm7 *)
  0x0f; 0x38; 0xcb; 0xd1;  (* sha256rnds2 xmm2,xmm1,xmm0 *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e; (* pshufd xmm0,xmm0,0xe *)
  0x48; 0x8d; 0x76; 0x40;  (* lea rsi,[rsi+0x40] *)
  0x0f; 0x38; 0xcc; 0xdc;  (* sha256msg1 xmm3,xmm4 *)
  0x0f; 0x38; 0xcb; 0xca;  (* sha256rnds2 xmm1,xmm2,xmm0 *)
  0x66; 0x0f; 0x6f; 0x41; 0xc0; (* movdqa xmm0,XMMWORD PTR [rcx-0x40] *)
  0x66; 0x0f; 0xfe; 0xc5;  (* paddd xmm0,xmm5 *)
  0x66; 0x0f; 0x38; 0x00; 0xf7; (* pshufb xmm6,xmm7 *)
  0x0f; 0x38; 0xcb; 0xd1;  (* sha256rnds2 xmm2,xmm1,xmm0 *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e; (* pshufd xmm0,xmm0,0xe *)
  0x66; 0x0f; 0x6f; 0xfe;  (* movdqa xmm7,xmm6 *)
  0x66; 0x0f; 0x3a; 0x0f; 0xfd; 0x04; (* palignr xmm7,xmm5,0x4 *)
  0x90;                    (* nop *)
  0x66; 0x0f; 0xfe; 0xdf;  (* paddd xmm3,xmm7 *)
  0x0f; 0x38; 0xcc; 0xe5;  (* sha256msg1 xmm4,xmm5 *)
  0x0f; 0x38; 0xcb; 0xca;  (* sha256rnds2 xmm1,xmm2,xmm0 *)
  0x66; 0x0f; 0x6f; 0x41; 0xe0; (* movdqa xmm0,XMMWORD PTR [rcx-0x20] *)
  0x66; 0x0f; 0xfe; 0xc6;  (* paddd xmm0,xmm6 *)
  0x0f; 0x38; 0xcd; 0xde;  (* sha256msg2 xmm3,xmm6 *)
  0x0f; 0x38; 0xcb; 0xd1;  (* sha256rnds2 xmm2,xmm1,xmm0 *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e; (* pshufd xmm0,xmm0,0xe *)
  0x66; 0x0f; 0x6f; 0xfb;  (* movdqa xmm7,xmm3 *)
  0x66; 0x0f; 0x3a; 0x0f; 0xfe; 0x04; (* palignr xmm7,xmm6,0x4 *)
  0x90;                    (* nop *)
  0x66; 0x0f; 0xfe; 0xe7;  (* paddd xmm4,xmm7 *)
  0x0f; 0x38; 0xcc; 0xee;  (* sha256msg1 xmm5,xmm6 *)
  0x0f; 0x38; 0xcb; 0xca;  (* sha256rnds2 xmm1,xmm2,xmm0 *)
  0x66; 0x0f; 0x6f; 0x01;  (* movdqa xmm0,XMMWORD PTR [rcx] *)
  0x66; 0x0f; 0xfe; 0xc3;  (* paddd xmm0,xmm3 *)
  0x0f; 0x38; 0xcd; 0xe3;  (* sha256msg2 xmm4,xmm3 *)
  0x0f; 0x38; 0xcb; 0xd1;  (* sha256rnds2 xmm2,xmm1,xmm0 *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e; (* pshufd xmm0,xmm0,0xe *)
  0x66; 0x0f; 0x6f; 0xfc;  (* movdqa xmm7,xmm4 *)
  0x66; 0x0f; 0x3a; 0x0f; 0xfb; 0x04; (* palignr xmm7,xmm3,0x4 *)
  0x90;                    (* nop *)
  0x66; 0x0f; 0xfe; 0xef;  (* paddd xmm5,xmm7 *)
  0x0f; 0x38; 0xcc; 0xf3;  (* sha256msg1 xmm6,xmm3 *)
  0x0f; 0x38; 0xcb; 0xca;  (* sha256rnds2 xmm1,xmm2,xmm0 *)
  0x66; 0x0f; 0x6f; 0x41; 0x20; (* movdqa xmm0,XMMWORD PTR [rcx+0x20] *)
  0x66; 0x0f; 0xfe; 0xc4;  (* paddd xmm0,xmm4 *)
  0x0f; 0x38; 0xcd; 0xec;  (* sha256msg2 xmm5,xmm4 *)
  0x0f; 0x38; 0xcb; 0xd1;  (* sha256rnds2 xmm2,xmm1,xmm0 *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e; (* pshufd xmm0,xmm0,0xe *)
  0x66; 0x0f; 0x6f; 0xfd;  (* movdqa xmm7,xmm5 *)
  0x66; 0x0f; 0x3a; 0x0f; 0xfc; 0x04; (* palignr xmm7,xmm4,0x4 *)
  0x90;                    (* nop *)
  0x66; 0x0f; 0xfe; 0xf7;  (* paddd xmm6,xmm7 *)
  0x0f; 0x38; 0xcc; 0xdc;  (* sha256msg1 xmm3,xmm4 *)
  0x0f; 0x38; 0xcb; 0xca;  (* sha256rnds2 xmm1,xmm2,xmm0 *)
  0x66; 0x0f; 0x6f; 0x41; 0x40; (* movdqa xmm0,XMMWORD PTR [rcx+0x40] *)
  0x66; 0x0f; 0xfe; 0xc5;  (* paddd xmm0,xmm5 *)
  0x0f; 0x38; 0xcd; 0xf5;  (* sha256msg2 xmm6,xmm5 *)
  0x0f; 0x38; 0xcb; 0xd1;  (* sha256rnds2 xmm2,xmm1,xmm0 *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e; (* pshufd xmm0,xmm0,0xe *)
  0x66; 0x0f; 0x6f; 0xfe;  (* movdqa xmm7,xmm6 *)
  0x66; 0x0f; 0x3a; 0x0f; 0xfd; 0x04; (* palignr xmm7,xmm5,0x4 *)
  0x90;                    (* nop *)
  0x66; 0x0f; 0xfe; 0xdf;  (* paddd xmm3,xmm7 *)
  0x0f; 0x38; 0xcc; 0xe5;  (* sha256msg1 xmm4,xmm5 *)
  0x0f; 0x38; 0xcb; 0xca;  (* sha256rnds2 xmm1,xmm2,xmm0 *)
  0x66; 0x0f; 0x6f; 0x41; 0x60; (* movdqa xmm0,XMMWORD PTR [rcx+0x60] *)
  0x66; 0x0f; 0xfe; 0xc6;  (* paddd xmm0,xmm6 *)
  0x0f; 0x38; 0xcd; 0xde;  (* sha256msg2 xmm3,xmm6 *)
  0x0f; 0x38; 0xcb; 0xd1;  (* sha256rnds2 xmm2,xmm1,xmm0 *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e; (* pshufd xmm0,xmm0,0xe *)
  0x66; 0x0f; 0x6f; 0xfb;  (* movdqa xmm7,xmm3 *)
  0x66; 0x0f; 0x3a; 0x0f; 0xfe; 0x04; (* palignr xmm7,xmm6,0x4 *)
  0x90;                    (* nop *)
  0x66; 0x0f; 0xfe; 0xe7;  (* paddd xmm4,xmm7 *)
  0x0f; 0x38; 0xcc; 0xee;  (* sha256msg1 xmm5,xmm6 *)
  0x0f; 0x38; 0xcb; 0xca;  (* sha256rnds2 xmm1,xmm2,xmm0 *)
  0x66; 0x0f; 0x6f; 0x81; 0x80; 0x00; 0x00; 0x00; (* movdqa xmm0,XMMWORD PTR [rcx+0x80] *)
  0x66; 0x0f; 0xfe; 0xc3;  (* paddd xmm0,xmm3 *)
  0x0f; 0x38; 0xcd; 0xe3;  (* sha256msg2 xmm4,xmm3 *)
  0x0f; 0x38; 0xcb; 0xd1;  (* sha256rnds2 xmm2,xmm1,xmm0 *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e; (* pshufd xmm0,xmm0,0xe *)
  0x66; 0x0f; 0x6f; 0xfc;  (* movdqa xmm7,xmm4 *)
  0x66; 0x0f; 0x3a; 0x0f; 0xfb; 0x04; (* palignr xmm7,xmm3,0x4 *)
  0x90;                    (* nop *)
  0x66; 0x0f; 0xfe; 0xef;  (* paddd xmm5,xmm7 *)
  0x0f; 0x38; 0xcc; 0xf3;  (* sha256msg1 xmm6,xmm3 *)
  0x0f; 0x38; 0xcb; 0xca;  (* sha256rnds2 xmm1,xmm2,xmm0 *)
  0x66; 0x0f; 0x6f; 0x81; 0xa0; 0x00; 0x00; 0x00; (* movdqa xmm0,XMMWORD PTR [rcx+0xa0] *)
  0x66; 0x0f; 0xfe; 0xc4;  (* paddd xmm0,xmm4 *)
  0x0f; 0x38; 0xcd; 0xec;  (* sha256msg2 xmm5,xmm4 *)
  0x0f; 0x38; 0xcb; 0xd1;  (* sha256rnds2 xmm2,xmm1,xmm0 *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e; (* pshufd xmm0,xmm0,0xe *)
  0x66; 0x0f; 0x6f; 0xfd;  (* movdqa xmm7,xmm5 *)
  0x66; 0x0f; 0x3a; 0x0f; 0xfc; 0x04; (* palignr xmm7,xmm4,0x4 *)
  0x90;                    (* nop *)
  0x66; 0x0f; 0xfe; 0xf7;  (* paddd xmm6,xmm7 *)
  0x0f; 0x38; 0xcc; 0xdc;  (* sha256msg1 xmm3,xmm4 *)
  0x0f; 0x38; 0xcb; 0xca;  (* sha256rnds2 xmm1,xmm2,xmm0 *)
  0x66; 0x0f; 0x6f; 0x81; 0xc0; 0x00; 0x00; 0x00; (* movdqa xmm0,XMMWORD PTR [rcx+0xc0] *)
  0x66; 0x0f; 0xfe; 0xc5;  (* paddd xmm0,xmm5 *)
  0x0f; 0x38; 0xcd; 0xf5;  (* sha256msg2 xmm6,xmm5 *)
  0x0f; 0x38; 0xcb; 0xd1;  (* sha256rnds2 xmm2,xmm1,xmm0 *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e; (* pshufd xmm0,xmm0,0xe *)
  0x66; 0x0f; 0x6f; 0xfe;  (* movdqa xmm7,xmm6 *)
  0x66; 0x0f; 0x3a; 0x0f; 0xfd; 0x04; (* palignr xmm7,xmm5,0x4 *)
  0x90;                    (* nop *)
  0x66; 0x0f; 0xfe; 0xdf;  (* paddd xmm3,xmm7 *)
  0x0f; 0x38; 0xcc; 0xe5;  (* sha256msg1 xmm4,xmm5 *)
  0x0f; 0x38; 0xcb; 0xca;  (* sha256rnds2 xmm1,xmm2,xmm0 *)
  0x66; 0x0f; 0x6f; 0x81; 0xe0; 0x00; 0x00; 0x00; (* movdqa xmm0,XMMWORD PTR [rcx+0xe0] *)
  0x66; 0x0f; 0xfe; 0xc6;  (* paddd xmm0,xmm6 *)
  0x0f; 0x38; 0xcd; 0xde;  (* sha256msg2 xmm3,xmm6 *)
  0x0f; 0x38; 0xcb; 0xd1;  (* sha256rnds2 xmm2,xmm1,xmm0 *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e; (* pshufd xmm0,xmm0,0xe *)
  0x66; 0x0f; 0x6f; 0xfb;  (* movdqa xmm7,xmm3 *)
  0x66; 0x0f; 0x3a; 0x0f; 0xfe; 0x04; (* palignr xmm7,xmm6,0x4 *)
  0x90;                    (* nop *)
  0x66; 0x0f; 0xfe; 0xe7;  (* paddd xmm4,xmm7 *)
  0x0f; 0x38; 0xcc; 0xee;  (* sha256msg1 xmm5,xmm6 *)
  0x0f; 0x38; 0xcb; 0xca;  (* sha256rnds2 xmm1,xmm2,xmm0 *)
  0x66; 0x0f; 0x6f; 0x81; 0x00; 0x01; 0x00; 0x00; (* movdqa xmm0,XMMWORD PTR [rcx+0x100] *)
  0x66; 0x0f; 0xfe; 0xc3;  (* paddd xmm0,xmm3 *)
  0x0f; 0x38; 0xcd; 0xe3;  (* sha256msg2 xmm4,xmm3 *)
  0x0f; 0x38; 0xcb; 0xd1;  (* sha256rnds2 xmm2,xmm1,xmm0 *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e; (* pshufd xmm0,xmm0,0xe *)
  0x66; 0x0f; 0x6f; 0xfc;  (* movdqa xmm7,xmm4 *)
  0x66; 0x0f; 0x3a; 0x0f; 0xfb; 0x04; (* palignr xmm7,xmm3,0x4 *)
  0x90;                    (* nop *)
  0x66; 0x0f; 0xfe; 0xef;  (* paddd xmm5,xmm7 *)
  0x0f; 0x38; 0xcc; 0xf3;  (* sha256msg1 xmm6,xmm3 *)
  0x0f; 0x38; 0xcb; 0xca;  (* sha256rnds2 xmm1,xmm2,xmm0 *)
  0x66; 0x0f; 0x6f; 0x81; 0x20; 0x01; 0x00; 0x00; (* movdqa xmm0,XMMWORD PTR [rcx+0x120] *)
  0x66; 0x0f; 0xfe; 0xc4;  (* paddd xmm0,xmm4 *)
  0x0f; 0x38; 0xcd; 0xec;  (* sha256msg2 xmm5,xmm4 *)
  0x0f; 0x38; 0xcb; 0xd1;  (* sha256rnds2 xmm2,xmm1,xmm0 *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e; (* pshufd xmm0,xmm0,0xe *)
  0x66; 0x0f; 0x6f; 0xfd;  (* movdqa xmm7,xmm5 *)
  0x66; 0x0f; 0x3a; 0x0f; 0xfc; 0x04; (* palignr xmm7,xmm4,0x4 *)
  0x0f; 0x38; 0xcb; 0xca;  (* sha256rnds2 xmm1,xmm2,xmm0 *)
  0x66; 0x0f; 0xfe; 0xf7;  (* paddd xmm6,xmm7 *)
  0x66; 0x0f; 0x6f; 0x81; 0x40; 0x01; 0x00; 0x00; (* movdqa xmm0,XMMWORD PTR [rcx+0x140] *)
  0x66; 0x0f; 0xfe; 0xc5;  (* paddd xmm0,xmm5 *)
  0x0f; 0x38; 0xcb; 0xd1;  (* sha256rnds2 xmm2,xmm1,xmm0 *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e; (* pshufd xmm0,xmm0,0xe *)
  0x0f; 0x38; 0xcd; 0xf5;  (* sha256msg2 xmm6,xmm5 *)
  0x66; 0x41; 0x0f; 0x6f; 0xf8; (* movdqa xmm7,xmm8 *)
  0x0f; 0x38; 0xcb; 0xca;  (* sha256rnds2 xmm1,xmm2,xmm0 *)
  0x66; 0x0f; 0x6f; 0x81; 0x60; 0x01; 0x00; 0x00; (* movdqa xmm0,XMMWORD PTR [rcx+0x160] *)
  0x66; 0x0f; 0xfe; 0xc6;  (* paddd xmm0,xmm6 *)
  0x90;                    (* nop *)
  0x0f; 0x38; 0xcb; 0xd1;  (* sha256rnds2 xmm2,xmm1,xmm0 *)
  0x66; 0x0f; 0x70; 0xc0; 0x0e; (* pshufd xmm0,xmm0,0xe *)
  0x48; 0xff; 0xca;        (* dec rdx *)
  0x90;                    (* nop *)
  0x0f; 0x38; 0xcb; 0xca;  (* sha256rnds2 xmm1,xmm2,xmm0 *)
  0x66; 0x41; 0x0f; 0xfe; 0xd2; (* paddd xmm2,xmm10 *)
  0x66; 0x41; 0x0f; 0xfe; 0xc9; (* paddd xmm1,xmm9 *)
  0x0f; 0x85; 0x26; 0xfd; 0xff; 0xff; (* jne 66 <Lsha256_compress_hw_oop_shaext> *)
  0x66; 0x0f; 0x70; 0xd2; 0xb1; (* pshufd xmm2,xmm2,0xb1 *)
  0x66; 0x0f; 0x70; 0xf9; 0x1b; (* pshufd xmm7,xmm1,0x1b *)
  0x66; 0x0f; 0x70; 0xc9; 0xb1; (* pshufd xmm1,xmm1,0xb1 *)
  0x66; 0x0f; 0x6d; 0xca;  (* punpckhqdq xmm1,xmm2 *)
  0x66; 0x0f; 0x3a; 0x0f; 0xd7; 0x08; (* palignr xmm2,xmm7,0x8 *)
  0xf3; 0x0f; 0x7f; 0x0f;  (* movdqu XMMWORD PTR [rdi],xmm1 *)
  0xf3; 0x0f; 0x7f; 0x57; 0x10; (* movdqu XMMWORD PTR [rdi+0x10],xmm2 *)
  0x0f; 0x10; 0x34; 0x24;  (* movups xmm6,XMMWORD PTR [rsp] *)
  0x0f; 0x10; 0x7c; 0x24; 0x10; (* movups xmm7,XMMWORD PTR [rsp+0x10] *)
  0x44; 0x0f; 0x10; 0x44; 0x24; 0x20; (* movups xmm8,XMMWORD PTR [rsp+0x20] *)
  0x44; 0x0f; 0x10; 0x4c; 0x24; 0x30; (* movups xmm9,XMMWORD PTR [rsp+0x30] *)
  0x44; 0x0f; 0x10; 0x54; 0x24; 0x40; (* movups xmm10,XMMWORD PTR [rsp+0x40] *)
  0x48; 0x83; 0xc4; 0x50;  (* add rsp,0x50 *)
  0x5e;                    (* pop rsi *)
  0x5f;                    (* pop rdi *)
  0xc3;                    (* ret *)
]]);;

let sha256_compress_hw_windows_tmc =
  define_trimmed "sha256_compress_hw_windows_tmc" sha256_compress_hw_windows_mc;;

let SHA256_COMPRESS_HW_WINDOWS_EXEC =
  X86_MK_EXEC_RULE sha256_compress_hw_windows_tmc;;

(* Phase 1 load marker: both objects are now decoded by the live              *)
(* define_assert_relocs_from_elf (SysV mc/tmc/EXEC + Windows mc/tmc/EXEC),    *)
(* proving the SHA-NI + SSE decode clauses cover the frozen byte streams.     *)
Printf.printf "SHA256_COMPRESS_HW Phase-1 loaded (SysV+Windows mc/tmc/EXEC decoded).\n%!";;

(* ========================================================================= *)
(* PHASE 2 - bridge lemmas from the SHA-NI primitives to the spec.           *)
(*                                                                           *)
(* The x86.ml SHA-NI semantics (sha256_rnds2_round / sha256_msg1 /           *)
(* sha256_msg2) are written with raw word primitives that are byte-for-byte  *)
(* the FIPS 180-4 Ch / Maj / big-Sigma / small-sigma formulas (see           *)
(* sha256_spec.ml sha_choose/sha_maj/sha_hash_sigma_0/1/sha_msg_sigma_0/1).  *)
(* The bridges below make that identity explicit so the assembly proof can   *)
(* refold each stepped SHA-NI instruction into the spec's sha256_round /     *)
(* message-schedule sigma at a cut-point.                                    *)
(*                                                                           *)
(* Tactic recipe (cheap - NO monolithic WORD_BLAST, which explodes on the    *)
(* 256-bit round with its carry chains + opaque Ch/Maj/sigma): unfold the     *)
(* primitive, TOP_DEPTH let_CONV, DEPTH EL_CONV, then HOL's ready-made        *)
(* WORD_SIMPLE_SUBWORD_CONV to reduce word_subword-of-word_join lane by lane  *)
(* (it auto-discharges the dimindex side-conditions), GSYM-fold the raw word  *)
(* chains back to the spec primitives, and close the now-identical pack with  *)
(* REWRITE_TAC[] (reflexive under the outer forall; plain REFL_TAC would fail *)
(* on the binder).                                                            *)
(* ------------------------------------------------------------------------- *)

(* Pack an 8-element working-state list [a;b;c;d;e;f;g;h] into the 256-bit    *)
(* {A..H} word the SHA-NI round primitive operates on (A at bits [224,32),    *)
(* H at [0,32)).                                                              *)
let PACK256 = new_definition
 `PACK256 (l:int32 list) : 256 word =
    (word_join:int32->224 word->256 word) (EL 0 l)
     ((word_join:int32->192 word->224 word) (EL 1 l)
      ((word_join:int32->160 word->192 word) (EL 2 l)
       ((word_join:int32->128 word->160 word) (EL 3 l)
        ((word_join:int32->96 word->128 word) (EL 4 l)
         ((word_join:int32->64 word->96 word) (EL 5 l)
          ((word_join:int32->32 word->64 word) (EL 6 l) (EL 7 l)))))))`;;

let PACK256_EXPLICIT = prove
 (`!a b c d e f g h:int32.
     PACK256 [a;b;c;d;e;f;g;h] =
     (word_join:int32->224 word->256 word) a
      ((word_join:int32->192 word->224 word) b
       ((word_join:int32->160 word->192 word) c
        ((word_join:int32->128 word->160 word) d
         ((word_join:int32->96 word->128 word) e
          ((word_join:int32->64 word->96 word) f
           ((word_join:int32->32 word->64 word) g h))))))`,
  REWRITE_TAC[PACK256] THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;

(* One SHA-NI round on the packed state = one spec sha256_round.  The round   *)
(* word wk = K_t + W_t is already summed, so feed word_add k w; the output    *)
(* pack [A'=t1+t2; a; b; c; E'=d+t1; e; f; g] matches sha256_round exactly.   *)
let SHA256_RNDS2_ROUND_BRIDGE = prove
 (`!a b c d e f g h k w:int32.
     sha256_rnds2_round (PACK256 [a;b;c;d;e;f;g;h]) (word_add k w) =
     PACK256 (sha256_round [a;b;c;d;e;f;g;h] k w)`,
  REWRITE_TAC[sha256_rnds2_round; sha256_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[PACK256_EXPLICIT] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[GSYM sha_choose; GSYM sha_maj;
              GSYM sha_hash_sigma_0; GSYM sha_hash_sigma_1] THEN
  REWRITE_TAC[]);;

(* SHA256MSG1 dst src: each output dword is W_i + sigma0(W_{i+1}).            *)
(* dst = {W3,W2,W1,W0} (W0 low), src low dword = W4.                          *)
let SHA256_MSG1_BRIDGE = prove
 (`!w0 w1 w2 w3 w4:int32.
     sha256_msg1
       ((word_join:int32->96 word->int128) w3
         ((word_join:int32->64 word->96 word) w2
           ((word_join:int32->32 word->64 word) w1 w0)))
       (word_zx w4 : int128) =
     (word_join:int32->96 word->int128) (word_add w3 (sha_msg_sigma_0 w4))
      ((word_join:int32->64 word->96 word) (word_add w2 (sha_msg_sigma_0 w3))
       ((word_join:int32->32 word->64 word) (word_add w1 (sha_msg_sigma_0 w2))
        (word_add w0 (sha_msg_sigma_0 w1))))`,
  REWRITE_TAC[sha256_msg1] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_TRIVIAL] THEN
  REWRITE_TAC[GSYM sha_msg_sigma_0] THEN
  REWRITE_TAC[]);;

(* SHA256MSG2 dst src: dst = {Wp3,Wp2,Wp1,Wp0} partial sums, src high two     *)
(* dwords = {W15,W14}.  Low two outputs chain sigma1 on W14,W15; high two     *)
(* chain on the freshly computed low results w16,w17.                         *)
let SHA256_MSG2_BRIDGE = prove
 (`!wp0 wp1 wp2 wp3 w14 w15 lo:int32.
     sha256_msg2
       ((word_join:int32->96 word->int128) wp3
         ((word_join:int32->64 word->96 word) wp2
           ((word_join:int32->32 word->64 word) wp1 wp0)))
       ((word_join:int32->96 word->int128) w15
         ((word_join:int32->64 word->96 word) w14
           (word_zx lo : 64 word)))  =
     (let w16 = word_add wp0 (sha_msg_sigma_1 w14) in
      let w17 = word_add wp1 (sha_msg_sigma_1 w15) in
      (word_join:int32->96 word->int128) (word_add wp3 (sha_msg_sigma_1 w17))
       ((word_join:int32->64 word->96 word) (word_add wp2 (sha_msg_sigma_1 w16))
        ((word_join:int32->32 word->64 word) w17 w16)))`,
  REWRITE_TAC[sha256_msg2] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_TRIVIAL] THEN
  REWRITE_TAC[GSYM sha_msg_sigma_1] THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* PSHUFB byteswap bridge (Phase-5 head/message-load enabler).                *)
(*                                                                            *)
(* The head byteswaps `pshufb xmm{3,4,5,6}, xmm7` reduce, via x86_PSHUFB, to  *)
(*   usimd16 (\i. if bit 7 i then word 0                                      *)
(*                else word_subword x (8 * val(word_subword i (0,4)),8)) ix   *)
(* where ix is the byte-shuffle control mask held in xmm7, loaded from        *)
(* .rodata+0x200 (= [rcx+0x180], rcx = K256+0x80).  That mask is the classic  *)
(* per-dword big-endian byteswap control                                      *)
(*   0f0e0d0c 0b0a0908 07060504 03020100  (little-endian dword layout)        *)
(* = the int128 literal below.  With an ABSTRACT mask usimd16 cannot reduce   *)
(* (probed s039); with the CONCRETE mask every control byte is a ground       *)
(* nibble, so WORD_REDUCE_CONV collapses the selector and the shuffle becomes *)
(* exactly a per-32-bit-lane word_bytereverse -- i.e. `usimd4 word_bytereverse`*)
(* which turns each raw little-endian message dword into its big-endian spec  *)
(* word (mirrors nohw's `word_bytereverse wraw`).                             *)
let PSHUFB_BYTESWAP = prove
 (`!x:int128.
     usimd16 (\i. if bit 7 i then word 0:byte
                  else word_subword x (8 * val (word_subword i (0,4):4 word),8))
             (word 16018520953223639909183530438118932995 : int128)
     = usimd4 word_bytereverse x`,
  let LANE = WORD_BLAST
    `word_bytereverse (w:int32) =
       (word_join:byte->24 word->int32) (word_subword w (0,8))
        ((word_join:byte->16 word->24 word) (word_subword w (8,8))
         ((word_join:byte->8 word->16 word) (word_subword w (16,8))
          (word_subword w (24,8))))` in
  GEN_TAC THEN
  CONV_TAC(LAND_CONV(
    REWRITE_CONV[usimd16;usimd8;usimd4;usimd2] THENC
    DEPTH_CONV DIMINDEX_CONV THENC DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
    WORD_REDUCE_CONV THENC DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
    NUM_REDUCE_CONV)) THEN
  CONV_TAC(RAND_CONV(
    REWRITE_CONV[usimd4;usimd2] THENC DEPTH_CONV DIMINDEX_CONV THENC
    DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
    ONCE_REWRITE_CONV[LANE] THENC DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  CONV_TAC WORD_BLAST);;

Printf.printf "SHA256_COMPRESS_HW PSHUFB_BYTESWAP loaded.\n%!";;

(* ------------------------------------------------------------------------- *)
(* The SHA256RNDS2 instruction does TWO spec rounds and operates on the       *)
(* ABEF/CDGH 128-bit lane split (A/C at bits [96,32) down to F/H at [0,32)),  *)
(* NOT the {A..H} 256-bit pack.  We package the instruction-level bridge as   *)
(* the composition of two spec rounds, keeping the working state as an        *)
(* abstract int32 list so the assembly proof can drive it at every round      *)
(* group.  ABEF_PACK/CDGH_PACK are the 128-bit register views.                *)
(* ------------------------------------------------------------------------- *)

let ABEF_PACK = new_definition
 `ABEF_PACK (a:int32) b e f : int128 =
    (word_join:int32->96 word->int128) a
     ((word_join:int32->64 word->96 word) b
       ((word_join:int32->32 word->64 word) e f))`;;

let CDGH_PACK = new_definition
 `CDGH_PACK (c:int32) d g h : int128 =
    (word_join:int32->96 word->int128) c
     ((word_join:int32->64 word->96 word) d
       ((word_join:int32->32 word->64 word) g h))`;;

(* DIRECT single-round bridge over an abstract list, round word wk fed as-is  *)
(* (k = word 0 so word_add k w = w).  The abstract l lets the LHS pattern     *)
(* `sha256_rnds2_round (PACK256 l) wk` match any packed argument.             *)
let RNDS2_ROUND_DIRECT = prove
 (`!l:int32 list. !wk:int32.
     sha256_rnds2_round (PACK256 l) wk =
     PACK256 (sha256_round l (word 0) wk)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[sha256_rnds2_round; sha256_round; PACK256] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN
  REWRITE_TAC[GSYM sha_choose; GSYM sha_maj;
              GSYM sha_hash_sigma_0; GSYM sha_hash_sigma_1] THEN
  REWRITE_TAC[]);;

(* The full 2-round SHA256RNDS2 instruction, as two composed spec rounds.     *)
(* src = ABEF of l, dst = CDGH of l, wk's low dword drives round 1 and its    *)
(* high dword drives round 2; the result is the new ABEF pack.                *)
let SHA256_RNDS2_BRIDGE = prove
 (`!l:int32 list. !wk:int128.
     sha256_rnds2 (CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l))
                  (ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l)) wk =
     (let l2 = sha256_round (sha256_round l (word 0) (word_subword wk (0,32)))
                            (word 0) (word_subword wk (32,32)) in
      ABEF_PACK (EL 0 l2) (EL 1 l2) (EL 4 l2) (EL 5 l2))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[sha256_rnds2; ABEF_PACK; CDGH_PACK] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[GSYM PACK256] THEN
  REWRITE_TAC[RNDS2_ROUND_DIRECT] THEN
  REWRITE_TAC[PACK256] THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[]);;

Printf.printf "SHA256_COMPRESS_HW Phase-2 bridge lemmas loaded (RNDS2/MSG1/MSG2).\n%!";;

(* ------------------------------------------------------------------------- *)
(* Smallest register-only 4-round-group ensures (Phase-2 workflow validation) *)
(*                                                                            *)
(* Fragment (trimmed-mc offsets, one 4-round unit of the loop body's round    *)
(* engine, register-only -- no memory, in-frame):                            *)
(*   pc+99   sha256rnds2 xmm2, xmm1      (dst CDGH, src ABEF, wk = xmm0)       *)
(*   pc+103  pshufd xmm0, xmm0, 0xe      (bring wk[64,128) down to [0,64))     *)
(*   pc+108  nop                                                              *)
(*   pc+109  movdqa xmm9, xmm1           (save ABEF for later feed-forward)    *)
(*   pc+114  sha256rnds2 xmm1, xmm2      (dst ABEF, src the new CDGH)          *)
(*   pc+118  <exit>                                                           *)
(*                                                                            *)
(* PROVEN (session 029).  The value leg closes with the workflow captured     *)
(* below.  KEY STATE SHAPE (session 028): after the first sha256rnds2 the      *)
(* stepper records                                                            *)
(*   read YMM2 s1 = word_join (word_subword (read YMM2 s0) (128,128))         *)
(*                            (sha256_rnds2 (word_subword (read YMM2 s0)(0,128)) *)
(*                                          (word_subword (read YMM1 s0)(0,128)) *)
(*                                          (word_subword (read YMM0 s0)(0,128))) *)
(* -- the VEX name `read YMM2` (256-bit, upper 128 preserved by SSE), with the *)
(* sha256_rnds2 args the low-128 subwords of the input YMMs.  So the           *)
(* postcondition is stated on `word_subword (read YMMi s) (0,128)` and closed  *)
(* by: X86_VERBOSE_STEP_TAC x5 (NOT X86_STEPS -- it discards the value facts), *)
(* ENSURES_FINAL_STATE_TAC, then rewrite the YMMi_SSE<->YMMi lens relation     *)
(* (READ_YMM_SSE_EQUIV, x86.ml) into both assumptions and goal, ASM_REWRITE    *)
(* to substitute the stepper facts, and WORD_SIMPLE_SUBWORD_CONV to collapse   *)
(* the word_subword(word_join ...) lenses.  The RIP and YMM2 legs then close   *)
(* by reflexivity; the YMM1 leg's round-2 round-key argument is the pshufd     *)
(* result {wk2,wk3,wk0,wk0} rather than the stated {wk2,wk3,0,0}, but          *)
(* sha256_rnds2 reads only wk's low 64 bits, so SHA256_RNDS2_WK_CONG           *)
(* discharges the difference.                                                  *)
(* ------------------------------------------------------------------------- *)

(* sha256_rnds2 uses its round-key argument wk only via word_subword (0,32)    *)
(* and (32,32) (the two round keys), so it is insensitive to wk's high 64      *)
(* bits.  Needed because the pshufd that supplies round 2's wk leaves the      *)
(* upper dwords as {wk0,wk0} (imm 0x0e = [2,3,0,0]) while the postcondition    *)
(* uses word_subword wk (64,64) (upper dwords zero).                           *)
let SHA256_RNDS2_WK_CONG = prove
 (`!d n w1 w2:int128.
     (word_subword w1 (0,32):int32 = word_subword w2 (0,32)) /\
     (word_subword w1 (32,32):int32 = word_subword w2 (32,32))
     ==> sha256_rnds2 d n w1 = sha256_rnds2 d n w2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[sha256_rnds2] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[]);;

let SHA256_COMPRESS_HW_GROUP4 = prove
 (`!pc kbase wk abef cdgh:int128.
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 99) /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) = (abef:int128) /\
            word_subword (read YMM2_SSE s) (0,128) = (cdgh:int128))
       (\s. read RIP s = word (pc + 118) /\
            word_subword (read YMM2_SSE s) (0,128) = sha256_rnds2 cdgh abef wk /\
            word_subword (read YMM1_SSE s) (0,128) =
              sha256_rnds2 abef (sha256_rnds2 cdgh abef wk)
                           (word_subword wk (64,64) : int128))
       (MAYCHANGE [RIP] ,, MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM9_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s5" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SHA256_RNDS2_WK_CONG THEN CONJ_TAC THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC);;

Printf.printf "SHA256_COMPRESS_HW Phase-2 group-4 ensures PROVEN (value leg cheat-free).\n%!";;

(* ------------------------------------------------------------------------- *)
(* Phase 3: the full repeating loop-body unit -- one message-schedule update  *)
(* interleaved with one 4-round group (register-only; the K+W load that feeds *)
(* it is memory and belongs to Phase 5).  Trimmed-mc offsets, one steady-state *)
(* iteration of the round engine (starting once K+W is already summed in xmm0):*)
(*   pc+208  sha256msg2 xmm3, xmm6        (schedule: xmm3' = msg2 W' W6)       *)
(*   pc+212  sha256rnds2 xmm2, xmm1       (round 1/2: dst CDGH, src ABEF)      *)
(*   pc+216  pshufd xmm0, xmm0, 0xe       (bring wk[64,128) down)             *)
(*   pc+221  movdqa xmm7, xmm3            (schedule scratch)                   *)
(*   pc+225  palignr xmm7, xmm6, 0x4      (schedule: byte-align for feed)      *)
(*   pc+231  nop                                                              *)
(*   pc+232  paddd xmm4, xmm7             (schedule: xmm4' = W4 + aligned)     *)
(*   pc+236  sha256msg1 xmm5, xmm6        (schedule: xmm5' = msg1 W5 W6)       *)
(*   pc+240  sha256rnds2 xmm1, xmm2       (round 2/2: dst ABEF, src new CDGH)  *)
(*   pc+244  <next K+W load>                                                   *)
(*                                                                            *)
(* THE REUSABLE PER-STEP REFOLD RECIPE (validated GROUP4 + this lemma):        *)
(* every SHA-NI op (sha256rnds2/msg1/msg2) records its write on the VEX name   *)
(* `read YMMi s` as `word_join (upper preserved) (op (low-128 subwords))`,     *)
(* while pre/post are stated on `word_subword (read YMMi_SSE s) (0,128)`.  The *)
(* closer that bridges the two names and collapses the lens plumbing:          *)
(*   X86_VERBOSE_STEP_TAC EXEC "sN"    (NOT X86_STEPS -- it discards values)   *)
(*   ENSURES_FINAL_STATE_TAC                                                   *)
(*   RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV)  (asms YMMi_SSE -> YMMi)  *)
(*   REWRITE_TAC READ_YMM_SSE_EQUIV                   (goal YMMi_SSE -> YMMi)  *)
(*   ASM_REWRITE_TAC[]                                (substitute step facts)  *)
(*   CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)    (collapse subword-join)  *)
(*   ASM_REWRITE_TAC[]                                (close reflexive legs)   *)
(* The only residual is any round whose round-key came through a pshufd (imm   *)
(* 0x0e = dwords {2,3,0,0}): its wk high 64 bits differ from word_subword wk   *)
(* (64,64) but sha256_rnds2 ignores them, discharged by SHA256_RNDS2_WK_CONG.  *)
(* palignr/paddd/pshufd need NO bridge -- WORD_SIMPLE_SUBWORD_CONV collapses    *)
(* them to pure word arithmetic; only the crypto primitives stay opaque.       *)
(* ------------------------------------------------------------------------- *)

let SHA256_COMPRESS_HW_SCHED_GROUP = prove
 (`!pc kbase wk abef cdgh w3 w4 w5 w6:int128.
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 208) /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) = (abef:int128) /\
            word_subword (read YMM2_SSE s) (0,128) = (cdgh:int128) /\
            word_subword (read YMM3_SSE s) (0,128) = (w3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (w4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (w5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (w6:int128))
       (\s. read RIP s = word (pc + 244) /\
            word_subword (read YMM2_SSE s) (0,128) = sha256_rnds2 cdgh abef wk /\
            word_subword (read YMM1_SSE s) (0,128) =
              sha256_rnds2 abef (sha256_rnds2 cdgh abef wk)
                           (word_subword wk (64,64) : int128) /\
            word_subword (read YMM3_SSE s) (0,128) = sha256_msg2 w3 w6 /\
            word_subword (read YMM5_SSE s) (0,128) = sha256_msg1 w5 w6)
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM5_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s5" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s6" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s7" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s8" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s9" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SHA256_RNDS2_WK_CONG THEN CONJ_TAC THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC);;

Printf.printf "SHA256_COMPRESS_HW Phase-3 schedule+round group PROVEN (cheat-free).\n%!";;

(* ========================================================================= *)
(* PHASE 4 -- crypto-accumulator algebra (the reusable per-group engine for   *)
(* the full 64-round core).                                                   *)
(*                                                                           *)
(* The round engine is 16 groups of 2x sha256rnds2 (= 4 spec rounds each).    *)
(* The crypto state lives in xmm1 = ABEF view, xmm2 = CDGH view of the        *)
(* working list.  The invariant is PERIOD-1 and self-maintaining: entering    *)
(* group g the registers hold xmm1 = ABEF_PACK(cr 4g), xmm2 = CDGH_PACK(cr 4g)*)
(* where cr n = sha256_compress_rounds m H n; the group's two chained rnds2   *)
(* advance to xmm1 = ABEF_PACK(cr 4(g+1)), xmm2 = CDGH_PACK(cr 4(g+1)).        *)
(*                                                                           *)
(* The three lemmas below capture the algebra ONCE so the per-group cut in    *)
(* the assembly proof (Phase 5+) is O(1):                                     *)
(*   CDGH_OF_TWO_ROUNDS       -- the round role-rotation identity that makes  *)
(*                               the group self-maintaining (CDGH after 2     *)
(*                               rounds = ABEF before).                       *)
(*   SHA256_ROUND_MERGE_KW    -- (k,w) collapses to (0, k+w), matching the    *)
(*                               assembly's paddd-then-rnds2 (k+w precomputed).*)
(*   SHA256_RNDS2_GROUP_ADVANCE -- one group's TWO rnds2 = FOUR spec rounds,   *)
(*                               stated on the ABEF/CDGH register views with   *)
(*                               the 128-bit round-key register wk (its four   *)
(*                               dwords are the four rounds' k+w; the pshufd    *)
(*                               that supplies rounds 3/4 is word_subword wk    *)
(*                               (64,64)).                                     *)
(* ------------------------------------------------------------------------- *)

(* After TWO spec rounds the state's CDGH lane {EL2,EL3,EL6,EL7} equals the   *)
(* input's ABEF lane {EL0,EL1,EL4,EL5} (rounds shift a->b->c, e->f->g); since *)
(* ABEF_PACK and CDGH_PACK share a body, CDGH_PACK(round^2 l) = ABEF_PACK l.   *)
let CDGH_OF_TWO_ROUNDS = prove
 (`!(l:int32 list) k0 k1:int32.
     CDGH_PACK
       (EL 2 (sha256_round (sha256_round l (word 0) k0) (word 0) k1))
       (EL 3 (sha256_round (sha256_round l (word 0) k0) (word 0) k1))
       (EL 6 (sha256_round (sha256_round l (word 0) k0) (word 0) k1))
       (EL 7 (sha256_round (sha256_round l (word 0) k0) (word 0) k1)) =
     ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ABEF_PACK; CDGH_PACK] THEN
  REWRITE_TAC[sha256_round] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;

(* sha256_round consumes k,w only via word_add k w, so the assembly's         *)
(* precomputed K+W (paddd) fed as w with k=0 equals the spec round with       *)
(* separate k,w.  Bridges the abstract-wk group advance to the spec's         *)
(* sha256_compress_rounds (which passes k = EL n consts, w = msg_schedule).   *)
let SHA256_ROUND_MERGE_KW = prove
 (`!(l:int32 list) k w:int32.
     sha256_round l (word 0) (word_add k w) = sha256_round l k w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sha256_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CONS_11] THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_RULE);;

(* The group advance: one round group = TWO chained sha256rnds2 = FOUR spec   *)
(* rounds.  wk's four dwords drive the four rounds ((0,32),(32,32) for the     *)
(* first rnds2; (64,32),(96,32) for the second, supplied by pshufd as         *)
(* word_subword wk (64,64)).  The second rnds2's dst is the OLD abef, which    *)
(* by CDGH_OF_TWO_ROUNDS is exactly CDGH(round^2 l) -- so it correctly plays   *)
(* the CDGH role for rounds 3/4.  Proof: two applications of                   *)
(* SHA256_RNDS2_BRIDGE, the second after rewriting the dst via                 *)
(* CDGH_OF_TWO_ROUNDS.                                                          *)
let SHA256_RNDS2_GROUP_ADVANCE = prove
 (`!(l:int32 list) wk:int128.
     let two = sha256_round
                 (sha256_round l (word 0) (word_subword wk (0,32)))
                 (word 0) (word_subword wk (32,32)) in
     let four = sha256_round
                  (sha256_round two (word 0) (word_subword wk (64,32)))
                  (word 0) (word_subword wk (96,32)) in
     sha256_rnds2 (CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l))
                  (ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l)) wk =
       ABEF_PACK (EL 0 two) (EL 1 two) (EL 4 two) (EL 5 two) /\
     sha256_rnds2 (ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l))
                  (ABEF_PACK (EL 0 two) (EL 1 two) (EL 4 two) (EL 5 two))
                  (word_subword wk (64,64) : int128) =
       ABEF_PACK (EL 0 four) (EL 1 four) (EL 4 four) (EL 5 four)`,
  REPEAT GEN_TAC THEN REPEAT LET_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[SHA256_RNDS2_BRIDGE] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN
      `ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 (l:int32 list)) (EL 5 l) =
       CDGH_PACK (EL 2 two) (EL 3 two) (EL 6 two) (EL 7 (two:int32 list))`
      SUBST1_TAC THENL
     [EXPAND_TAC "two" THEN REWRITE_TAC[CDGH_OF_TWO_ROUNDS];
      ALL_TAC] THEN
    REWRITE_TAC[SHA256_RNDS2_BRIDGE] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    ASM_REWRITE_TAC[]]);;

(* xmm2 after the group holds CDGH_PACK(four): the first rnds2 leaves xmm2 =   *)
(* ABEF_PACK(two), and CDGH_OF_TWO_ROUNDS (with l:=two) gives ABEF_PACK(two) = *)
(* CDGH_PACK(round^2 two) = CDGH_PACK(four).  Keeps the ABEF/CDGH invariant     *)
(* self-consistent across the group boundary.                                 *)
let ABEF_TWO_IS_CDGH_FOUR = prove
 (`!(l:int32 list) k0 k1 k2 k3:int32.
     (let two = sha256_round (sha256_round l (word 0) k0) (word 0) k1 in
      let four = sha256_round (sha256_round two (word 0) k2) (word 0) k3 in
      ABEF_PACK (EL 0 two) (EL 1 two) (EL 4 two) (EL 5 two) =
      CDGH_PACK (EL 2 four) (EL 3 four) (EL 6 four) (EL 7 four))`,
  REPEAT GEN_TAC THEN REPEAT LET_TAC THEN
  EXPAND_TAC "four" THEN REWRITE_TAC[CDGH_OF_TWO_ROUNDS]);;

(* CR4 l wk = advance the working list l by ONE round group (four spec rounds) *)
(* driven by the 128-bit round-key register wk (its four dwords are the four   *)
(* rounds' k+w).  The per-group state-advance atom for the 64-round core:      *)
(* after group g the crypto registers hold ABEF_PACK/CDGH_PACK of CR4 applied  *)
(* g+1 times to the initial working list.                                     *)
let CR4 = new_definition
 `CR4 (l:int32 list) (wk:int128) : int32 list =
    sha256_round
      (sha256_round
        (sha256_round
          (sha256_round l (word 0) (word_subword wk (0,32)))
          (word 0) (word_subword wk (32,32)))
        (word 0) (word_subword wk (64,32)))
      (word 0) (word_subword wk (96,32))`;;

(* THE PACKED GROUP CUT LEMMA -- the Phase-4 composable unit.  Same ensures as *)
(* GROUP4 but with pre/post in ABEF/CDGH accumulator form over an abstract     *)
(* working list l: entering xmm1=ABEF_PACK(l), xmm2=CDGH_PACK(l), round-key    *)
(* xmm0=wk, the group advances four spec rounds to xmm1=ABEF_PACK(CR4 l wk),   *)
(* xmm2=CDGH_PACK(CR4 l wk).  Derived from GROUP4 by rewriting the packed post *)
(* BACKWARDS into raw sha256_rnds2 (NO re-stepping of the 24KB SHA-NI output). *)
let SHA256_COMPRESS_HW_GROUP4_PACKED = prove
 (`!pc kbase (l:int32 list) (wk:int128).
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 99) /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l))
       (\s. read RIP s = word (pc + 118) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (CR4 l wk)) (EL 3 (CR4 l wk))
                        (EL 6 (CR4 l wk)) (EL 7 (CR4 l wk)) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (CR4 l wk)) (EL 1 (CR4 l wk))
                        (EL 4 (CR4 l wk)) (EL 5 (CR4 l wk)))
       (MAYCHANGE [RIP] ,, MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM9_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  let GA = CONV_RULE(TOP_DEPTH_CONV let_CONV)
             (SPECL [`l:int32 list`; `wk:int128`] SHA256_RNDS2_GROUP_ADVANCE) in
  let GA1 = CONJUNCT1 GA and GA2 = CONJUNCT2 GA in
  let ATCF = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`l:int32 list`;
             `word_subword wk (0,32):int32`; `word_subword wk (32,32):int32`;
             `word_subword wk (64,32):int32`; `word_subword wk (96,32):int32`]
            ABEF_TWO_IS_CDGH_FOUR) in
  REPEAT GEN_TAC THEN REWRITE_TAC[CR4] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA2] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM ATCF] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA1] THEN
  MATCH_ACCEPT_TAC SHA256_COMPRESS_HW_GROUP4);;

Printf.printf "SHA256_COMPRESS_HW Phase-4 crypto-accumulator algebra PROVEN.\n%!";;

(* ------------------------------------------------------------------------- *)
(* Phase-4 SPEC CONNECTION -- CR4 group-advance = FOUR sha256_compress_rounds. *)
(*                                                                           *)
(* The crypto-accumulator engine advances the ABEF/CDGH working list by CR4    *)
(* per group given the round-key register wk.  Here we tie CR4 to the spec's   *)
(* sha256_compress_rounds so that iterating 16 groups yields                   *)
(* sha256_compress_rounds m H 64.  wk's four dwords must equal K_t + W_t for   *)
(* the four rounds of the group (the assembly's paddd of the doubled K row     *)
(* and the byteswapped/scheduled message quad); SHA256_ROUND_MERGE_KW then     *)
(* collapses each (0, K+W) to (K, W) matching the spec round.                  *)
(* ------------------------------------------------------------------------- *)

(* Peel one compress round in SUC form. *)
let COMPRESS_ROUNDS_SUC = prove
 (`!(m:int32 list) hsh n.
     sha256_compress_rounds m hsh (SUC n) =
     sha256_round (sha256_compress_rounds m hsh n)
                  (EL n sha256_constants) (sha256_msg_schedule m n)`,
  REWRITE_TAC[ADD1; sha256_compress_rounds]);;

(* Unfold FOUR compress rounds at once, indices normalised uniformly to SUC. *)
let COMPRESS_ROUNDS_ADD4 = prove
 (`!(m:int32 list) hsh n.
     sha256_compress_rounds m hsh (n + 4) =
     sha256_round
      (sha256_round
       (sha256_round
        (sha256_round (sha256_compress_rounds m hsh n)
           (EL n sha256_constants) (sha256_msg_schedule m n))
        (EL (n+1) sha256_constants) (sha256_msg_schedule m (n+1)))
       (EL (n+2) sha256_constants) (sha256_msg_schedule m (n+2)))
      (EL (n+3) sha256_constants) (sha256_msg_schedule m (n+3))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `n + 4 = SUC(n+3)`; ARITH_RULE `n + 3 = SUC(n+2)`;
              ARITH_RULE `n + 2 = SUC(n+1)`; ARITH_RULE `n + 1 = SUC n`] THEN
  REWRITE_TAC[COMPRESS_ROUNDS_SUC]);;

(* The spec-connection lemma: one CR4 group from the state after n rounds,     *)
(* driven by wk = the four (K_t + W_t) dwords, equals four compress rounds.    *)
let CR4_COMPRESS_STEP = prove
 (`!(m:int32 list) l n (wk:int128).
     word_subword wk (0,32) =
       word_add (EL n sha256_constants) (sha256_msg_schedule m n) /\
     word_subword wk (32,32) =
       word_add (EL (n+1) sha256_constants) (sha256_msg_schedule m (n+1)) /\
     word_subword wk (64,32) =
       word_add (EL (n+2) sha256_constants) (sha256_msg_schedule m (n+2)) /\
     word_subword wk (96,32) =
       word_add (EL (n+3) sha256_constants) (sha256_msg_schedule m (n+3))
     ==> CR4 (sha256_compress_rounds m l n) wk =
         sha256_compress_rounds m l (n + 4)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[COMPRESS_ROUNDS_ADD4; CR4] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SHA256_ROUND_MERGE_KW]);;

Printf.printf "SHA256_COMPRESS_HW Phase-4 spec connection (CR4 = 4 compress rounds) PROVEN.\n%!";;

(* ========================================================================= *)
(* PHASE 4 -- W-RING SCHEDULE ALGEBRA (the message-schedule half of the       *)
(* engine, dual to the crypto-accumulator algebra above).                     *)
(*                                                                           *)
(* The four message registers xmm3,xmm4,xmm5,xmm6 hold consecutive 4-dword    *)
(* windows of the schedule and rotate period-4.  Each group updates one       *)
(* register to the NEXT window via the staggered pipeline (OpenSSL shaext):   *)
(*   sha256msg1 Qk, Q(k+1)      -- lane i: W_i + sigma0(W_{i+1})              *)
(*   paddd      _ , palignr(Q(k+3),Q(k+2),4)  -- adds {W_{t-7}} = the         *)
(*                                 4 dwords {W(4k+9)..W(4k+12)}                *)
(*   sha256msg2 _ , Q(k+3)      -- adds sigma1(W_{t-2}); high lanes chain      *)
(*                                 on the freshly computed low results        *)
(* yielding Q(k+4) = {W(4k+16)..W(4k+19)}.                                     *)
(*                                                                           *)
(* WQUAD packs a 4-dword schedule window (w0 lowest), matching the msg1/msg2  *)
(* bridge dst pattern.  The three quad-level op lemmas collapse the model     *)
(* SIMD ops onto WQUAD packs; WRING_STEP composes them and ties the result to *)
(* sha256_msg_schedule, so that after group g the ring holds the correct      *)
(* schedule window.  This discharges CR4_COMPRESS_STEP's wk = K + W hypothesis *)
(* at the quad level in the assembly proof.                                    *)
(* ------------------------------------------------------------------------- *)

(* A 4-dword schedule window packed into a 128-bit register, w0 in the low    *)
(* dword (right-associated word_join, matching SHA256_MSG1/MSG2_BRIDGE).      *)
let WQUAD = new_definition
 `WQUAD (w0:int32) w1 w2 w3 : int128 =
    (word_join:int32->96 word->int128) w3
     ((word_join:int32->64 word->96 word) w2
       ((word_join:int32->32 word->64 word) w1 w0))`;;

(* Any int128 is the WQUAD of its four dwords.  Used to reconcile the         *)
(* nested-join (2x2) shape that simd4/palignr produce with the right-assoc    *)
(* WQUAD chain that msg1/msg2 consume.                                        *)
let WQUAD_EXPAND = prove
 (`!x:int128. WQUAD (word_subword x (0,32)) (word_subword x (32,32))
                    (word_subword x (64,32)) (word_subword x (96,32)) = x`,
  GEN_TAC THEN REWRITE_TAC[WQUAD] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_JOIN; BIT_WORD_SUBWORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REPEAT COND_CASES_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `0 + i = i`;
               ARITH_RULE `~(i < 32) ==> (32 + i - 32 = i)`;
               ARITH_RULE `~(i < 64) ==> (64 + i - 64 = i)`;
               ARITH_RULE `~(i < 96) ==> (96 + i - 96 = i)`;
               ARITH_RULE `i < 64 ==> (i - 32 < 32 <=> T)`;
               ARITH_RULE `i < 96 ==> (i - 64 < 32 <=> T)`;
               ARITH_RULE `i < 128 ==> (i - 96 < 32 <=> T)`] THEN
  ASM_REWRITE_TAC[]);;

(* WQUAD is injective: equality of packs reduces to the four dword equalities. *)
let WQUAD_INJ = prove
 (`!a0 a1 a2 a3 b0 b1 b2 b3:int32.
     WQUAD a0 a1 a2 a3 = WQUAD b0 b1 b2 b3 <=>
     a0 = b0 /\ a1 = b1 /\ a2 = b2 /\ a3 = b3`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(fun th ->
      MP_TAC(AP_TERM `\z:int128. word_subword z (0,32):int32` th) THEN
      MP_TAC(AP_TERM `\z:int128. word_subword z (32,32):int32` th) THEN
      MP_TAC(AP_TERM `\z:int128. word_subword z (64,32):int32` th) THEN
      MP_TAC(AP_TERM `\z:int128. word_subword z (96,32):int32` th)) THEN
    REWRITE_TAC[WQUAD] THEN
    CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[] THEN MESON_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* One-step schedule recurrence in offset form (FIPS 180-4 sec. 6.2.2), and    *)
(* the same recurrence re-associated to match the pipeline's add order.        *)
let SCHED_REC = prove
 (`!(m:int32 list) n. 16 <= n ==>
     sha256_msg_schedule m n =
     word_add
       (word_add (sha_msg_sigma_1 (sha256_msg_schedule m (n - 2)))
                 (sha256_msg_schedule m (n - 7)))
       (word_add (sha_msg_sigma_0 (sha256_msg_schedule m (n - 15)))
                 (sha256_msg_schedule m (n - 16)))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [sha256_msg_schedule] THEN
  ASM_SIMP_TAC[ARITH_RULE `16 <= n ==> ~(n < 16)`]);;

let SCHED_REC_ASSOC = prove
 (`!(m:int32 list) n. 16 <= n ==>
     sha256_msg_schedule m n =
     word_add
       (word_add
          (word_add (sha256_msg_schedule m (n - 16))
                    (sha_msg_sigma_0 (sha256_msg_schedule m (n - 15))))
          (sha256_msg_schedule m (n - 7)))
       (sha_msg_sigma_1 (sha256_msg_schedule m (n - 2)))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [sha256_msg_schedule] THEN
  ASM_SIMP_TAC[ARITH_RULE `16 <= n ==> ~(n < 16)`] THEN
  CONV_TAC WORD_RULE);;

(* sha256msg1 over two schedule quads: dst={w0..w3}, src low=w4.  Output lane  *)
(* i = w_i + sigma0(w_{i+1}) (the sigma0(W_{t-15}) + W_{t-16} partial).         *)
let MSG1_QUAD = prove
 (`!w0 w1 w2 w3 w4 x y z:int32.
     sha256_msg1 (WQUAD w0 w1 w2 w3) (WQUAD w4 x y z) =
     WQUAD (word_add w0 (sha_msg_sigma_0 w1))
           (word_add w1 (sha_msg_sigma_0 w2))
           (word_add w2 (sha_msg_sigma_0 w3))
           (word_add w3 (sha_msg_sigma_0 w4))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sha256_msg1; WQUAD] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[sha_msg_sigma_0] THEN REWRITE_TAC[]);;

(* palignr dst=Q3 src=Q2 imm=4 (byte count 4 = one dword): concat Q3:Q2, shift *)
(* right 4 bytes, take low 128 = {Q2[1],Q2[2],Q2[3],Q3[0]} -- the {W_{t-7}}    *)
(* window.  Reduces the raw word_subword(word_ushr(join)) via the subword      *)
(* algebra (WORD_USHR_AS_SUBWORD + WORD_SUBWORD_SUBWORD) then WQUAD_EXPAND.     *)
let PALIGNR4_QUAD = prove
 (`!a0 a1 a2 a3 b0 b1 b2 b3:int32.
     word_subword
       (word_ushr
          ((word_join:int128->int128->256 word) (WQUAD b0 b1 b2 b3)
                                                 (WQUAD a0 a1 a2 a3))
          (8 * 4))
       (0,128) : int128 =
     WQUAD a1 a2 a3 b0`,
  REPEAT GEN_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  SIMP_TAC[WORD_USHR_AS_SUBWORD; WORD_SUBWORD_SUBWORD;
           DIMINDEX_128; DIMINDEX_256; ARITH] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MIN_CONV) THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM WQUAD_EXPAND] THEN
  REWRITE_TAC[WQUAD] THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[]);;

(* Fused paddd-then-sha256msg2 over quads: dst of msg2 is the lane-wise sum of *)
(* the msg1 partials {m_i} and the palignr {W_{t-7}} terms {p_i}; src holds    *)
(* {_,_,w14,w15} for the sigma1 terms.  Low two outputs chain sigma1 on w14,   *)
(* w15; high two chain on the freshly computed low results.  simd4 produces a  *)
(* nested-join int128 but msg2 re-extracts by word_subword, so the shape is    *)
(* irrelevant -- the whole thing collapses in one pass.                        *)
let MSG2_PADDD_QUAD = prove
 (`!m0 m1 m2 m3 p0 p1 p2 p3 aa bb w14 w15:int32.
     sha256_msg2
       (simd4 word_add (WQUAD m0 m1 m2 m3) (WQUAD p0 p1 p2 p3))
       (WQUAD aa bb w14 w15) =
     (let q0 = word_add (word_add m0 p0) (sha_msg_sigma_1 w14) in
      let q1 = word_add (word_add m1 p1) (sha_msg_sigma_1 w15) in
      WQUAD q0 q1
            (word_add (word_add m2 p2) (sha_msg_sigma_1 q0))
            (word_add (word_add m3 p3) (sha_msg_sigma_1 q1)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sha256_msg2; WQUAD; simd4; simd2] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[sha_msg_sigma_1] THEN REWRITE_TAC[]);;

(* THE W-RING STEP.  The full staggered schedule pipeline, over four           *)
(* consecutive schedule windows at offset n, produces exactly the next window  *)
(* {W(n+16)..W(n+19)}.  This is the schedule analogue of CR4_COMPRESS_STEP:    *)
(* iterating it 12 times (windows are refreshed every group after the first    *)
(* 16 message words are loaded) keeps the ring holding the correct schedule.   *)
(* Note the palignr t-7 terms come from Q(k+3):Q(k+2) = {W(n+8)..W(n+15)}      *)
(* shifted, giving {W(n+9),W(n+10),W(n+11),W(n+12)}.                            *)
let WRING_STEP = prove
 (`!(m:int32 list) n.
     sha256_msg2
       (simd4 word_add
          (sha256_msg1
             (WQUAD (sha256_msg_schedule m n) (sha256_msg_schedule m (n+1))
                    (sha256_msg_schedule m (n+2)) (sha256_msg_schedule m (n+3)))
             (WQUAD (sha256_msg_schedule m (n+4)) (sha256_msg_schedule m (n+5))
                    (sha256_msg_schedule m (n+6)) (sha256_msg_schedule m (n+7))))
          (word_subword
             (word_ushr
                ((word_join:int128->int128->256 word)
                   (WQUAD (sha256_msg_schedule m (n+12)) (sha256_msg_schedule m (n+13))
                          (sha256_msg_schedule m (n+14)) (sha256_msg_schedule m (n+15)))
                   (WQUAD (sha256_msg_schedule m (n+8)) (sha256_msg_schedule m (n+9))
                          (sha256_msg_schedule m (n+10)) (sha256_msg_schedule m (n+11))))
                (8 * 4))
             (0,128)))
       (WQUAD (sha256_msg_schedule m (n+12)) (sha256_msg_schedule m (n+13))
              (sha256_msg_schedule m (n+14)) (sha256_msg_schedule m (n+15)))
     = WQUAD (sha256_msg_schedule m (n+16)) (sha256_msg_schedule m (n+17))
             (sha256_msg_schedule m (n+18)) (sha256_msg_schedule m (n+19))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[PALIGNR4_QUAD; MSG1_QUAD] THEN
  REWRITE_TAC[MSG2_PADDD_QUAD] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WQUAD_INJ] THEN
  SUBGOAL_THEN
   `word_add (word_add (word_add (sha256_msg_schedule m n)
                (sha_msg_sigma_0 (sha256_msg_schedule m (n + 1))))
             (sha256_msg_schedule m (n + 9)))
             (sha_msg_sigma_1 (sha256_msg_schedule m (n + 14)))
    = sha256_msg_schedule m (n + 16)`
   ASSUME_TAC THENL
   [MP_TAC(SPECL [`m:int32 list`; `n + 16`] SCHED_REC_ASSOC) THEN
    REWRITE_TAC[ARITH_RULE `16 <= n + 16`;
      ARITH_RULE `(n + 16) - 16 = n`; ARITH_RULE `(n + 16) - 15 = n + 1`;
      ARITH_RULE `(n + 16) - 7 = n + 9`; ARITH_RULE `(n + 16) - 2 = n + 14`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (word_add (sha256_msg_schedule m (n + 1))
                (sha_msg_sigma_0 (sha256_msg_schedule m (n + 2))))
             (sha256_msg_schedule m (n + 10)))
             (sha_msg_sigma_1 (sha256_msg_schedule m (n + 15)))
    = sha256_msg_schedule m (n + 17)`
   ASSUME_TAC THENL
   [MP_TAC(SPECL [`m:int32 list`; `n + 17`] SCHED_REC_ASSOC) THEN
    REWRITE_TAC[ARITH_RULE `16 <= n + 17`;
      ARITH_RULE `(n + 17) - 16 = n + 1`; ARITH_RULE `(n + 17) - 15 = n + 2`;
      ARITH_RULE `(n + 17) - 7 = n + 10`; ARITH_RULE `(n + 17) - 2 = n + 15`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`m:int32 list`; `n + 18`] SCHED_REC_ASSOC) THEN
    REWRITE_TAC[ARITH_RULE `16 <= n + 18`;
      ARITH_RULE `(n + 18) - 16 = n + 2`; ARITH_RULE `(n + 18) - 15 = n + 3`;
      ARITH_RULE `(n + 18) - 7 = n + 11`; ARITH_RULE `(n + 18) - 2 = n + 16`] THEN
    DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    MP_TAC(SPECL [`m:int32 list`; `n + 19`] SCHED_REC_ASSOC) THEN
    REWRITE_TAC[ARITH_RULE `16 <= n + 19`;
      ARITH_RULE `(n + 19) - 16 = n + 3`; ARITH_RULE `(n + 19) - 15 = n + 4`;
      ARITH_RULE `(n + 19) - 7 = n + 12`; ARITH_RULE `(n + 19) - 2 = n + 17`] THEN
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

Printf.printf "SHA256_COMPRESS_HW Phase-4 W-ring schedule algebra PROVEN.\n%!";;

(* ========================================================================= *)
(* PHASE 4 -- ASSEMBLY COMPOSITION building blocks (the 16-group core).       *)
(*                                                                           *)
(* The 16-group monolithic ensures cuts at the K-load boundaries.  Every     *)
(* group begins with the two-instruction round-key setup                     *)
(*   movdqa xmm0,[rcx+disp]     (load the doubled K row for rounds 4g..4g+3)  *)
(*   paddd  xmm0,xmmW           (add the scheduled/byteswapped message quad)  *)
(* leaving xmm0 = wk = K_quad + W_quad, the 128-bit round-key register that   *)
(* SHA256_COMPRESS_HW_GROUP4_PACKED / SCHED_GROUP consume.                    *)
(*                                                                           *)
(* CRUCIAL ISA FACT (session 032): the K-load is MOVDQA, whose x86.ml         *)
(* semantics are guarded by `aligned_OPERAND128 src s` (x86.ml L3189-3195):   *)
(* if the 16-byte source address is not provably 16-aligned the semantics     *)
(* collapse to `\s'. F` and the symbolic stepper SPINS trying to reason about *)
(* the faulting branch (one such step ran >200 s of CPU with no progress).    *)
(* So a K-load atom MUST carry `aligned 16 <Kaddr>` as a precondition -- true *)
(* in reality since rcx = K256+128 and the K256 rodata blob is 16-aligned;    *)
(* the alignment is discharged ONCE at the top wrapper from the K256 base.    *)
(* (The entry state loads at 0x0b/0x0f and the message loads at 0x3c.. use    *)
(* MOVDQU, which has no alignment guard -- that is why no earlier register-    *)
(* only group lemma ever hit this.)                                           *)
(*                                                                           *)
(* The atom below is the group-4 representative (K-load at trimmed pc+0xf4,   *)
(* disp 0 = [rcx], adding xmm3); the other 15 groups differ only in the       *)
(* K-load displacement, the added message register (period-4 xmm3/4/5/6) and  *)
(* the entry PC (session-031 group-boundary table).  The value leg closes by  *)
(* expanding simd4;simd2 (the paddd lane split) in the goal so both sides      *)
(* reduce to the same four-dword word_join, then the standard YMMi_SSE<->YMMi  *)
(* lens rewrite + WORD_SIMPLE_SUBWORD_CONV.                                    *)
(* ------------------------------------------------------------------------- *)

let SHA256_COMPRESS_HW_KLOAD4 = prove
 (`!pc kbase rcx kq wq:int128.
     aligned 16 rcx
     ==> ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0xf4) /\
            read RCX s = rcx /\
            read (memory :> bytes128 rcx) s = kq /\
            word_subword (read YMM3_SSE s) (0,128) = (wq:int128))
       (\s. read RIP s = word (pc + 0xfc) /\
            word_subword (read YMM0_SSE s) (0,128) = simd4 word_add kq wq)
       (MAYCHANGE [RIP] ,, MAYCHANGE [YMM0_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[]);;

Printf.printf "SHA256_COMPRESS_HW Phase-4 K-load atom (aligned MOVDQA + paddd) PROVEN.\n%!";;

(* ------------------------------------------------------------------------- *)
(* THE STEADY-STATE GROUP STEP (register-only, abstract wk).  One full        *)
(* iteration of the round engine's repeating body, entered AFTER the K+W sum  *)
(* is already in xmm0 (that paddd is the KLOAD4 atom above): the two chained   *)
(* sha256rnds2 (4 spec rounds) interleaved with one schedule-ring update.      *)
(* This is the r=0 rotation representative (groups 4,8,12): message registers  *)
(* xmm3(held),xmm4(msg2),xmm5(paddd),xmm6(msg1).  Entry trimmed pc+0xfc        *)
(* (sha256msg2, right after the paddd), exit pc+0x120 (round-2/2 rnds2, right  *)
(* BEFORE the next group's K-load MOVDQA).                                     *)
(*                                                                           *)
(* Structurally identical to SHA256_COMPRESS_HW_SCHED_GROUP (Phase 3) -- same  *)
(* 9-instruction unit, different entry PC and register rotation -- and closed  *)
(* by the identical 9x VERBOSE-step + refold closer.  CRITICAL: use            *)
(* X86_VERBOSE_STEP_TAC (NOT X86_STEPS_TAC): the latter's internal             *)
(* DISCARD_OLDSTATE_TAC erases the folded sha256_rnds2 forms, forcing the      *)
(* final WORD_SIMPLE_SUBWORD_CONV to descend the raw ~24KB nested-rnds2 crypto *)
(* tree (>10 min -> holctl client timeout); and a 10th step would land on the  *)
(* unaligned next-group memory MOVDQA and spin (session-032).  Exactly 9 steps.*)
(* The composition with the K+W formation (KLOAD4) yields the full group.      *)
(* ------------------------------------------------------------------------- *)

let SHA256_COMPRESS_HW_GROUP_STEP4 = prove
 (`!pc kbase wk abef cdgh a3 a4 a5 a6:int128.
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0xfc) /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) = (abef:int128) /\
            word_subword (read YMM2_SSE s) (0,128) = (cdgh:int128) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (\s. read RIP s = word (pc + 0x120) /\
            word_subword (read YMM2_SSE s) (0,128) = sha256_rnds2 cdgh abef wk /\
            word_subword (read YMM1_SSE s) (0,128) =
              sha256_rnds2 abef (sha256_rnds2 cdgh abef wk)
                           (word_subword wk (64,64) : int128) /\
            word_subword (read YMM4_SSE s) (0,128) = sha256_msg2 a4 a3 /\
            word_subword (read YMM6_SSE s) (0,128) = sha256_msg1 a6 a3)
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM4_SSE; YMM5_SSE; YMM6_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s5" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s6" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s7" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s8" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s9" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SHA256_RNDS2_WK_CONG THEN CONJ_TAC THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC);;

Printf.printf "SHA256_COMPRESS_HW Phase-4 steady-state group-step (r=0) PROVEN.\n%!";;

(* The r=1 and r=2 rotations of the same steady-state group-step.  The message *)
(* ring xmm3,xmm4,xmm5,xmm6 rotates period-4, so the four groups differ only in *)
(* which register plays the held/msg2/paddd/msg1 role and in the entry PC.      *)
(* r=0 = GROUP_STEP4 above (groups 4,8,12), r=3 = SCHED_GROUP (Phase 3, groups   *)
(* 3,7,11).  These two complete the set (r=1 groups 5,9,13; r=2 groups 6,10).    *)
(* PCs + register maps verified against objdump (tmc = objdump - 4).            *)
(*   r=1: entry pc+0x129, exit pc+0x14d; held xmm4, msg2 xmm5, paddd xmm6,       *)
(*        msg1 xmm3.                                                            *)
(*   r=2: entry pc+0x156, exit pc+0x17a; held xmm5, msg2 xmm6, paddd xmm3,       *)
(*        msg1 xmm4.                                                            *)
(* Identical 9x VERBOSE-step + refold closer.                                   *)

let SHA256_COMPRESS_HW_GROUP_STEP4_R1 = prove
 (`!pc kbase wk abef cdgh a3 a4 a5 a6:int128.
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x129) /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) = (abef:int128) /\
            word_subword (read YMM2_SSE s) (0,128) = (cdgh:int128) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (\s. read RIP s = word (pc + 0x14d) /\
            word_subword (read YMM2_SSE s) (0,128) = sha256_rnds2 cdgh abef wk /\
            word_subword (read YMM1_SSE s) (0,128) =
              sha256_rnds2 abef (sha256_rnds2 cdgh abef wk)
                           (word_subword wk (64,64) : int128) /\
            word_subword (read YMM5_SSE s) (0,128) = sha256_msg2 a5 a4 /\
            word_subword (read YMM3_SSE s) (0,128) = sha256_msg1 a3 a4)
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM5_SSE; YMM6_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s5" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s6" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s7" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s8" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s9" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SHA256_RNDS2_WK_CONG THEN CONJ_TAC THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC);;

Printf.printf "SHA256_COMPRESS_HW Phase-4 steady-state group-step (r=1) PROVEN.\n%!";;

let SHA256_COMPRESS_HW_GROUP_STEP4_R2 = prove
 (`!pc kbase wk abef cdgh a3 a4 a5 a6:int128.
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x156) /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) = (abef:int128) /\
            word_subword (read YMM2_SSE s) (0,128) = (cdgh:int128) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (\s. read RIP s = word (pc + 0x17a) /\
            word_subword (read YMM2_SSE s) (0,128) = sha256_rnds2 cdgh abef wk /\
            word_subword (read YMM1_SSE s) (0,128) =
              sha256_rnds2 abef (sha256_rnds2 cdgh abef wk)
                           (word_subword wk (64,64) : int128) /\
            word_subword (read YMM6_SSE s) (0,128) = sha256_msg2 a6 a5 /\
            word_subword (read YMM4_SSE s) (0,128) = sha256_msg1 a4 a5)
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM6_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s5" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s6" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s7" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s8" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s9" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SHA256_RNDS2_WK_CONG THEN CONJ_TAC THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC);;

Printf.printf "SHA256_COMPRESS_HW Phase-4 steady-state group-step (r=2) PROVEN.\n%!";;

(* ------------------------------------------------------------------------- *)
(* PACKED steady-state group-steps -- the composable units the 16-group       *)
(* monolith chains.  Each is derived from the corresponding raw group-step by  *)
(* the SAME backwards-rewrite as GROUP4_PACKED (GA1/GA2/ATCF + MATCH_ACCEPT):  *)
(* the crypto post (xmm1,xmm2) is rewritten from raw nested sha256_rnds2 into   *)
(* the ABEF/CDGH_PACK accumulator form over CR4 l wk (period-1 invariant), and *)
(* the two schedule conjuncts (msg2/msg1, already the clean form WRING_STEP     *)
(* consumes) pass through untouched.  No re-stepping of the 24KB SHA-NI output. *)
(* The register roles rotate period-4 across r=0..3, so each packed step names  *)
(* different msg registers; the crypto leg is identical.                       *)
(* ------------------------------------------------------------------------- *)

let SHA256_COMPRESS_HW_GROUP_STEP4_PACKED = prove
 (`!pc kbase (l:int32 list) (wk:int128) a3 a4 a5 a6:int128.
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0xfc) /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (\s. read RIP s = word (pc + 0x120) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (CR4 l wk)) (EL 3 (CR4 l wk))
                        (EL 6 (CR4 l wk)) (EL 7 (CR4 l wk)) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (CR4 l wk)) (EL 1 (CR4 l wk))
                        (EL 4 (CR4 l wk)) (EL 5 (CR4 l wk)) /\
            word_subword (read YMM4_SSE s) (0,128) = sha256_msg2 a4 a3 /\
            word_subword (read YMM6_SSE s) (0,128) = sha256_msg1 a6 a3)
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM4_SSE; YMM5_SSE; YMM6_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  let GA = CONV_RULE(TOP_DEPTH_CONV let_CONV)
             (SPECL [`l:int32 list`; `wk:int128`] SHA256_RNDS2_GROUP_ADVANCE) in
  let GA1 = CONJUNCT1 GA and GA2 = CONJUNCT2 GA in
  let ATCF = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`l:int32 list`;
             `word_subword wk (0,32):int32`; `word_subword wk (32,32):int32`;
             `word_subword wk (64,32):int32`; `word_subword wk (96,32):int32`]
            ABEF_TWO_IS_CDGH_FOUR) in
  REPEAT GEN_TAC THEN REWRITE_TAC[CR4] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA2] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM ATCF] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA1] THEN
  MATCH_ACCEPT_TAC SHA256_COMPRESS_HW_GROUP_STEP4);;

Printf.printf "SHA256_COMPRESS_HW Phase-4 packed group-step (r=0) PROVEN.\n%!";;

(* The packing tactic factored out: given a raw group-step lemma whose crypto   *)
(* post is the two nested sha256_rnds2, rewrite the goal's packed post BACKWARDS *)
(* into that raw form and MATCH_ACCEPT the raw lemma.  Reused for r=1,2,3.       *)
let PACK_GROUP_STEP_TAC raw =
  (fun (asl,w) ->
   (let GA = CONV_RULE(TOP_DEPTH_CONV let_CONV)
               (SPECL [`l:int32 list`; `wk:int128`] SHA256_RNDS2_GROUP_ADVANCE) in
    let GA1 = CONJUNCT1 GA and GA2 = CONJUNCT2 GA in
    let ATCF = CONV_RULE(TOP_DEPTH_CONV let_CONV)
      (ISPECL [`l:int32 list`;
               `word_subword wk (0,32):int32`; `word_subword wk (32,32):int32`;
               `word_subword wk (64,32):int32`; `word_subword wk (96,32):int32`]
              ABEF_TWO_IS_CDGH_FOUR) in
    (REPEAT GEN_TAC THEN REWRITE_TAC[CR4] THEN
     GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA2] THEN
     GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM ATCF] THEN
     GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA1] THEN
     MATCH_ACCEPT_TAC raw)) (asl,w));;

let SHA256_COMPRESS_HW_GROUP_STEP4_R1_PACKED = prove
 (`!pc kbase (l:int32 list) (wk:int128) a3 a4 a5 a6:int128.
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x129) /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (\s. read RIP s = word (pc + 0x14d) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (CR4 l wk)) (EL 3 (CR4 l wk))
                        (EL 6 (CR4 l wk)) (EL 7 (CR4 l wk)) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (CR4 l wk)) (EL 1 (CR4 l wk))
                        (EL 4 (CR4 l wk)) (EL 5 (CR4 l wk)) /\
            word_subword (read YMM5_SSE s) (0,128) = sha256_msg2 a5 a4 /\
            word_subword (read YMM3_SSE s) (0,128) = sha256_msg1 a3 a4)
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM5_SSE; YMM6_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  PACK_GROUP_STEP_TAC SHA256_COMPRESS_HW_GROUP_STEP4_R1);;

Printf.printf "SHA256_COMPRESS_HW Phase-4 packed group-step (r=1) PROVEN.\n%!";;

let SHA256_COMPRESS_HW_GROUP_STEP4_R2_PACKED = prove
 (`!pc kbase (l:int32 list) (wk:int128) a3 a4 a5 a6:int128.
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x156) /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (\s. read RIP s = word (pc + 0x17a) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (CR4 l wk)) (EL 3 (CR4 l wk))
                        (EL 6 (CR4 l wk)) (EL 7 (CR4 l wk)) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (CR4 l wk)) (EL 1 (CR4 l wk))
                        (EL 4 (CR4 l wk)) (EL 5 (CR4 l wk)) /\
            word_subword (read YMM6_SSE s) (0,128) = sha256_msg2 a6 a5 /\
            word_subword (read YMM4_SSE s) (0,128) = sha256_msg1 a4 a5)
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM6_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  PACK_GROUP_STEP_TAC SHA256_COMPRESS_HW_GROUP_STEP4_R2);;

Printf.printf "SHA256_COMPRESS_HW Phase-4 packed group-step (r=2) PROVEN.\n%!";;

(* r=3 is the committed SCHED_GROUP (entry pc+208, exit pc+244).  Held reg is   *)
(* xmm6 (msg2 SRC), msg2 dst xmm3=w3, msg1 dst xmm5=w5; xmm4=w4 is scratch.      *)
let SHA256_COMPRESS_HW_SCHED_GROUP_PACKED = prove
 (`!pc kbase (l:int32 list) (wk:int128) w3 w4 w5 w6:int128.
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 208) /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
            word_subword (read YMM3_SSE s) (0,128) = (w3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (w4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (w5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (w6:int128))
       (\s. read RIP s = word (pc + 244) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (CR4 l wk)) (EL 3 (CR4 l wk))
                        (EL 6 (CR4 l wk)) (EL 7 (CR4 l wk)) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (CR4 l wk)) (EL 1 (CR4 l wk))
                        (EL 4 (CR4 l wk)) (EL 5 (CR4 l wk)) /\
            word_subword (read YMM3_SSE s) (0,128) = sha256_msg2 w3 w6 /\
            word_subword (read YMM5_SSE s) (0,128) = sha256_msg1 w5 w6)
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM5_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  PACK_GROUP_STEP_TAC SHA256_COMPRESS_HW_SCHED_GROUP);;

Printf.printf "SHA256_COMPRESS_HW Phase-4 packed group-step (r=3) PROVEN.\n%!";;

(* ------------------------------------------------------------------------- *)
(* THE FULL-GROUP COMPOSE ATOM (r=0) -- the reusable per-group unit the        *)
(* 16-cut monolith folds.  One complete round group, tmc pc+0xf4 .. pc+0x120:  *)
(*   pc+0xf4  movdqa xmm0,[rcx]     (K-load, the doubled K row for this group)  *)
(*   pc+0xf8  paddd  xmm0,xmm3      (wk = K_quad + W_quad)                      *)
(*   pc+0xfc..0x120  the packed steady-state group-step (2 rnds2 + ring update) *)
(* Cut at the seam pc+0xfc via ENSURES_SEQUENCE_TAC (nohw HEAD-monolith idiom): *)
(*   leg 1 = the K-load (2 verbose steps + KLOAD4 closer), establishing         *)
(*           xmm0 = simd4 word_add kq a3; the unchanged YMM1..6 conjuncts ride  *)
(*           through via ASM_REWRITE_TAC[];                                     *)
(*   leg 2 = GROUP_STEP4_PACKED instantiated wk := simd4 word_add kq a3, which  *)
(*           is alpha-identical to the leg, closed by MATCH_ACCEPT_TAC.         *)
(* CRUCIAL: the wk = simd4 word_add kq a3 is ABSTRACT to the crypto -- simd4    *)
(* appears ONLY as CR4's round-key argument, never threaded into the nested     *)
(* rnds2 tree.  (The pc+0xf4 monolithic-11-step variant was abandoned because   *)
(* it unfolded simd4 inside the crypto and broke SHA256_RNDS2_WK_CONG.)         *)
(* This atom demonstrates the full monolith composition mechanics for one       *)
(* steady-state group; the 16-group ensures folds it (+ the other 3 rotations)  *)
(* with per-group K-displacement, entry PC and register rotation from the       *)
(* session-031 group-boundary table.                                           *)
(* ------------------------------------------------------------------------- *)

let SHA256_COMPRESS_HW_GROUP4_FULL = prove
 (`!pc kbase rcx (l:int32 list) (kq:int128) a3 a4 a5 a6:int128.
     aligned 16 rcx
     ==> ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0xf4) /\
            read RCX s = rcx /\
            read (memory :> bytes128 rcx) s = kq /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (\s. read RIP s = word (pc + 0x120) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (CR4 l (simd4 word_add kq a3)))
                        (EL 3 (CR4 l (simd4 word_add kq a3)))
                        (EL 6 (CR4 l (simd4 word_add kq a3)))
                        (EL 7 (CR4 l (simd4 word_add kq a3))) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (CR4 l (simd4 word_add kq a3)))
                        (EL 1 (CR4 l (simd4 word_add kq a3)))
                        (EL 4 (CR4 l (simd4 word_add kq a3)))
                        (EL 5 (CR4 l (simd4 word_add kq a3))) /\
            word_subword (read YMM4_SSE s) (0,128) = sha256_msg2 a4 a3 /\
            word_subword (read YMM6_SSE s) (0,128) = sha256_msg1 a6 a3)
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM4_SSE; YMM5_SSE; YMM6_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0xfc`
   `\s. word_subword (read YMM0_SSE s) (0,128) = simd4 word_add kq a3 /\
        word_subword (read YMM1_SSE s) (0,128) =
          ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
        word_subword (read YMM2_SSE s) (0,128) =
          CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
        word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
        word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
        word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
        word_subword (read YMM6_SSE s) (0,128) = (a6:int128)` THEN
  CONJ_TAC THENL
   [(* leg 1: K-load, pc+0xf4 .. pc+0xfc *)
    ENSURES_INIT_TAC "s0" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
    REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[];
    (* leg 2: the packed group-step at pc+0xfc with wk := simd4 word_add kq a3 *)
    MATCH_ACCEPT_TAC(REWRITE_RULE[SOME_FLAGS]
      (SPECL
        [`pc:num`; `kbase:num`; `l:int32 list`; `simd4 word_add kq a3 :int128`;
         `a3:int128`; `a4:int128`; `a5:int128`; `a6:int128`]
        SHA256_COMPRESS_HW_GROUP_STEP4_PACKED))]);;

Printf.printf "SHA256_COMPRESS_HW Phase-4 full-group compose atom (r=0) PROVEN.\n%!";;

(* ------------------------------------------------------------------------- *)
(* THE COMPOSABLE SEAM ATOMS (session 035).  The group-step lemmas above      *)
(* state only YMM1/YMM2 (crypto) + YMM4 (msg2) + YMM6 (msg1) in the post; the *)
(* code's `paddd xmm5,xmm7` also updates YMM5 (the in-flight paddd partial     *)
(* ring register) and YMM3 stays held -- both left in MAYCHANGE but UNSTATED. *)
(* For a real group-to-group composition the NEXT group reads all four ring   *)
(* registers, so the seam predicate must carry them.  GROUP_STEP4_S is the    *)
(* r=0 step strengthened to state ALL FOUR ring registers in the post.  The   *)
(* extra YMM5 conjunct is the folded `simd4 word_add a5 (palignr ...)` form    *)
(* (what MSG2_PADDD_QUAD / WRING_STEP consume next group); its value leg       *)
(* closes by expanding simd4;simd2 on the goal so both sides reduce to the     *)
(* same four-dword lane word_join (mirrors KLOAD4's paddd closer).            *)
(* ------------------------------------------------------------------------- *)

let SHA256_COMPRESS_HW_GROUP_STEP4_S = prove
 (`!pc kbase wk abef cdgh a3 a4 a5 a6:int128.
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0xfc) /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) = (abef:int128) /\
            word_subword (read YMM2_SSE s) (0,128) = (cdgh:int128) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (\s. read RIP s = word (pc + 0x120) /\
            word_subword (read YMM2_SSE s) (0,128) = sha256_rnds2 cdgh abef wk /\
            word_subword (read YMM1_SSE s) (0,128) =
              sha256_rnds2 abef (sha256_rnds2 cdgh abef wk)
                           (word_subword wk (64,64) : int128) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = sha256_msg2 a4 a3 /\
            word_subword (read YMM5_SSE s) (0,128) =
              simd4 word_add a5
                (word_subword
                   (word_ushr
                      ((word_join:int128->int128->256 word) (sha256_msg2 a4 a3) a3)
                      (8 * 4)) (0,128)) /\
            word_subword (read YMM6_SSE s) (0,128) = sha256_msg1 a6 a3)
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM4_SSE; YMM5_SSE; YMM6_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s5" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s6" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s7" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s8" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s9" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC SHA256_RNDS2_WK_CONG THEN CONJ_TAC THEN
      CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC) THEN
  TRY REFL_TAC);;

Printf.printf "SHA256_COMPRESS_HW Phase-4 strengthened group-step (r=0, all rings) PROVEN.\n%!";;

(* ------------------------------------------------------------------------- *)
(* Memory-threaded strengthened steps (session 035): GROUP_STEP4_S + also    *)
(* carrying the unchanged RCX and a generic read-only bytes128 (the NEXT      *)
(* group's K quad) pre->post.  Both absent from every MAYCHANGE, so they ride *)
(* the frame.  This lets the full-group seam atom's step leg be a clean       *)
(* MATCH_ACCEPT with the pointer/K-memory already threaded.  _PACKED derived   *)
(* by the same backwards-rewrite (GA1/GA2/ATCF) as the committed packed steps. *)
(* ------------------------------------------------------------------------- *)

let SHA256_COMPRESS_HW_GROUP_STEP4_SM = prove
 (`!pc kbase rcx mloc (mval:int128) wk abef cdgh a3 a4 a5 a6:int128.
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0xfc) /\
            read RCX s = rcx /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) = (abef:int128) /\
            word_subword (read YMM2_SSE s) (0,128) = (cdgh:int128) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (\s. read RIP s = word (pc + 0x120) /\
            read RCX s = rcx /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM2_SSE s) (0,128) = sha256_rnds2 cdgh abef wk /\
            word_subword (read YMM1_SSE s) (0,128) =
              sha256_rnds2 abef (sha256_rnds2 cdgh abef wk)
                           (word_subword wk (64,64) : int128) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = sha256_msg2 a4 a3 /\
            word_subword (read YMM5_SSE s) (0,128) =
              simd4 word_add a5
                (word_subword
                   (word_ushr
                      ((word_join:int128->int128->256 word) (sha256_msg2 a4 a3) a3)
                      (8 * 4)) (0,128)) /\
            word_subword (read YMM6_SSE s) (0,128) = sha256_msg1 a6 a3)
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM4_SSE; YMM5_SSE; YMM6_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s5" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s6" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s7" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s8" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s9" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC SHA256_RNDS2_WK_CONG THEN CONJ_TAC THEN
      CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC) THEN
  TRY REFL_TAC);;

Printf.printf "SHA256_COMPRESS_HW Phase-4 mem-threaded group-step (r=0) PROVEN.\n%!";;

(* Packed form: crypto post rewritten to ABEF/CDGH_PACK(CR4 l wk); RCX/mem      *)
(* and schedule conjuncts pass through untouched.  Same PACK_GROUP_STEP_TAC     *)
(* backwards-rewrite as the committed packed steps.                            *)
let SHA256_COMPRESS_HW_GROUP_STEP4_SM_PACKED = prove
 (`!pc kbase rcx mloc (mval:int128) (l:int32 list) (wk:int128) a3 a4 a5 a6:int128.
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0xfc) /\
            read RCX s = rcx /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (\s. read RIP s = word (pc + 0x120) /\
            read RCX s = rcx /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (CR4 l wk)) (EL 3 (CR4 l wk))
                        (EL 6 (CR4 l wk)) (EL 7 (CR4 l wk)) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (CR4 l wk)) (EL 1 (CR4 l wk))
                        (EL 4 (CR4 l wk)) (EL 5 (CR4 l wk)) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = sha256_msg2 a4 a3 /\
            word_subword (read YMM5_SSE s) (0,128) =
              simd4 word_add a5
                (word_subword
                   (word_ushr
                      ((word_join:int128->int128->256 word) (sha256_msg2 a4 a3) a3)
                      (8 * 4)) (0,128)) /\
            word_subword (read YMM6_SSE s) (0,128) = sha256_msg1 a6 a3)
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM4_SSE; YMM5_SSE; YMM6_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  let GA = CONV_RULE(TOP_DEPTH_CONV let_CONV)
             (SPECL [`l:int32 list`; `wk:int128`] SHA256_RNDS2_GROUP_ADVANCE) in
  let GA1 = CONJUNCT1 GA and GA2 = CONJUNCT2 GA in
  let ATCF = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`l:int32 list`;
             `word_subword wk (0,32):int32`; `word_subword wk (32,32):int32`;
             `word_subword wk (64,32):int32`; `word_subword wk (96,32):int32`]
            ABEF_TWO_IS_CDGH_FOUR) in
  REPEAT GEN_TAC THEN REWRITE_TAC[CR4] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA2] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM ATCF] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA1] THEN
  MATCH_ACCEPT_TAC SHA256_COMPRESS_HW_GROUP_STEP4_SM);;

Printf.printf "SHA256_COMPRESS_HW Phase-4 mem-threaded packed group-step (r=0) PROVEN.\n%!";;

Printf.printf "S035_STEP_SM_PACKED hyps=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_GROUP_STEP4_SM_PACKED));;

(* ------------------------------------------------------------------------- *)
(* THE STRENGTHENED FULL-GROUP SEAM ATOM (r=0, session 035).  One complete    *)
(* group pc+0xf4 -> pc+0x120 (= NEXT group's K-load entry), cut at pc+0xfc.   *)
(* Unlike GROUP4_FULL it states ALL FOUR ring registers YMM3..6 in the post   *)
(* AND threads the unchanged RCX + the NEXT group's read-only K quad          *)
(* (mem @ rcx+32) pre->post -- the EXACT seam predicate the next group's      *)
(* K-load (movdqa xmm0,[rcx+32]; paddd xmm0,xmmW) consumes.  leg 1 = K-load    *)
(* (KLOAD4 closer, RCX/Kmem/YMM1..6 ride the frame); leg 2 = GROUP_STEP4_SM_   *)
(* PACKED (bare MATCH_ACCEPT, matcher instantiates the binders).  This is the  *)
(* seam-carrying unit the multi-group composition chains.                     *)
(* ------------------------------------------------------------------------- *)

let SHA256_COMPRESS_HW_GROUP4_FULL_S = prove
 (`!pc kbase (kptr:int64) (l:int32 list) (kq:int128) (kq1:int128) a3 a4 a5 a6:int128.
     aligned 16 kptr
     ==> ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0xf4) /\
            read RCX s = kptr /\
            read (memory :> bytes128 kptr) s = kq /\
            read (memory :> bytes128 (word_add kptr (word 32))) s = kq1 /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (\s. read RIP s = word (pc + 0x120) /\
            read RCX s = kptr /\
            read (memory :> bytes128 (word_add kptr (word 32))) s = kq1 /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (CR4 l (simd4 word_add kq a3)))
                        (EL 3 (CR4 l (simd4 word_add kq a3)))
                        (EL 6 (CR4 l (simd4 word_add kq a3)))
                        (EL 7 (CR4 l (simd4 word_add kq a3))) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (CR4 l (simd4 word_add kq a3)))
                        (EL 1 (CR4 l (simd4 word_add kq a3)))
                        (EL 4 (CR4 l (simd4 word_add kq a3)))
                        (EL 5 (CR4 l (simd4 word_add kq a3))) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = sha256_msg2 a4 a3 /\
            word_subword (read YMM5_SSE s) (0,128) =
              simd4 word_add a5
                (word_subword
                   (word_ushr
                      ((word_join:int128->int128->256 word) (sha256_msg2 a4 a3) a3)
                      (8 * 4)) (0,128)) /\
            word_subword (read YMM6_SSE s) (0,128) = sha256_msg1 a6 a3)
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM4_SSE; YMM5_SSE; YMM6_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0xfc`
   `\s. read RCX s = kptr /\
        read (memory :> bytes128 (word_add kptr (word 32))) s = kq1 /\
        word_subword (read YMM0_SSE s) (0,128) = simd4 word_add kq a3 /\
        word_subword (read YMM1_SSE s) (0,128) =
          ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
        word_subword (read YMM2_SSE s) (0,128) =
          CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
        word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
        word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
        word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
        word_subword (read YMM6_SSE s) (0,128) = (a6:int128)` THEN
  CONJ_TAC THENL
   [(* leg 1: K-load pc+0xf4 .. pc+0xfc; RCX/Kmem@kptr+32/YMM1..6 ride through *)
    ENSURES_INIT_TAC "s0" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
    REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[];
    (* leg 2: the memory-threaded packed group-step, wk := simd4 word_add kq a3.  *)
    (* Bare MATCH_ACCEPT lets the higher-order matcher instantiate the binders    *)
    (* from the leg goal (mloc := kptr+32, wk := simd4 word_add kq a3, etc.),      *)
    (* avoiding a hand-typed SPECL of the polymorphic simd4 term.                 *)
    MATCH_ACCEPT_TAC(REWRITE_RULE[SOME_FLAGS]
        SHA256_COMPRESS_HW_GROUP_STEP4_SM_PACKED)]);;


Printf.printf "SHA256_COMPRESS_HW Phase-4 strengthened full-group seam atom (r=0) PROVEN.\n%!";;

(* ------------------------------------------------------------------------- *)
(* The r=1 rotation of the strengthened seam atoms (session 035).  Same       *)
(* shape as the r=0 SM / FULL_S atoms, rotated one message register: r=1       *)
(* holds xmm4 (wk source), msg2 xmm5, paddd xmm6 (the in-flight partial),      *)
(* msg1 xmm3.  FULL_S_R1 is one complete r=1 group pc+0x120 -> pc+0x14d         *)
(* (K-load [rcx+0x20] + xmm4, then the r=1 step).  These are the second        *)
(* rotation the multi-group composition chains after GROUP4_FULL_S.            *)
(* ------------------------------------------------------------------------- *)

let SHA256_COMPRESS_HW_GROUP_STEP4_SM_R1 = prove
 (`!pc kbase (kptr:int64) mloc (mval:int128) wk abef cdgh (a3:int128) (a4:int128) (a5:int128) (a6:int128).
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x129) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) = (abef:int128) /\
            word_subword (read YMM2_SSE s) (0,128) = (cdgh:int128) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (\s. read RIP s = word (pc + 0x14d) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM2_SSE s) (0,128) = sha256_rnds2 cdgh abef wk /\
            word_subword (read YMM1_SSE s) (0,128) =
              sha256_rnds2 abef (sha256_rnds2 cdgh abef wk)
                           (word_subword wk (64,64) : int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = sha256_msg2 a5 a4 /\
            word_subword (read YMM6_SSE s) (0,128) =
              simd4 word_add a6
                (word_subword
                   (word_ushr
                      ((word_join:int128->int128->256 word) (sha256_msg2 a5 a4) a4)
                      (8 * 4)) (0,128)) /\
            word_subword (read YMM3_SSE s) (0,128) = sha256_msg1 a3 a4)
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM5_SSE; YMM6_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s5" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s6" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s7" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s8" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s9" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC SHA256_RNDS2_WK_CONG THEN CONJ_TAC THEN
      CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC) THEN
  TRY REFL_TAC);;

Printf.printf "SHA256_COMPRESS_HW Phase-4 mem-threaded group-step (r=1) PROVEN.\n%!";;

let SHA256_COMPRESS_HW_GROUP_STEP4_SM_R1_PACKED = prove
 (`!pc kbase (kptr:int64) mloc (mval:int128) (l:int32 list) (wk:int128) (a3:int128) (a4:int128) (a5:int128) (a6:int128).
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x129) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (\s. read RIP s = word (pc + 0x14d) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (CR4 l wk)) (EL 3 (CR4 l wk))
                        (EL 6 (CR4 l wk)) (EL 7 (CR4 l wk)) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (CR4 l wk)) (EL 1 (CR4 l wk))
                        (EL 4 (CR4 l wk)) (EL 5 (CR4 l wk)) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = sha256_msg2 a5 a4 /\
            word_subword (read YMM6_SSE s) (0,128) =
              simd4 word_add a6
                (word_subword
                   (word_ushr
                      ((word_join:int128->int128->256 word) (sha256_msg2 a5 a4) a4)
                      (8 * 4)) (0,128)) /\
            word_subword (read YMM3_SSE s) (0,128) = sha256_msg1 a3 a4)
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM5_SSE; YMM6_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  let GA = CONV_RULE(TOP_DEPTH_CONV let_CONV)
             (SPECL [`l:int32 list`; `wk:int128`] SHA256_RNDS2_GROUP_ADVANCE) in
  let GA1 = CONJUNCT1 GA and GA2 = CONJUNCT2 GA in
  let ATCF = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`l:int32 list`;
             `word_subword wk (0,32):int32`; `word_subword wk (32,32):int32`;
             `word_subword wk (64,32):int32`; `word_subword wk (96,32):int32`]
            ABEF_TWO_IS_CDGH_FOUR) in
  REPEAT GEN_TAC THEN REWRITE_TAC[CR4] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA2] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM ATCF] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA1] THEN
  MATCH_ACCEPT_TAC SHA256_COMPRESS_HW_GROUP_STEP4_SM_R1);;

Printf.printf "SHA256_COMPRESS_HW Phase-4 mem-threaded packed group-step (r=1) PROVEN.\n%!";;

(* ---- r=1 full-group seam atom: K-load[rcx+0x20]+xmm4 ⨾ step_R1 ------------ *)
(* g5 K-load: pc+0x120 movdqa xmm0,[rcx+0x20]; pc+0x125 paddd xmm0,xmm4.        *)
(* Entry pc+0x120, exit pc+0x14d.  wk = simd4 word_add kq1 a4 (a4 = held xmm4). *)
(* Threads RCX + the NEXT-next K quad (mem @ rcx+0x40) for a further group.     *)
let SHA256_COMPRESS_HW_GROUP4_FULL_S_R1 = prove
 (`!pc kbase (kptr:int64) (l:int32 list) (kq1:int128) (kq2:int128) (a3:int128) (a4:int128) (a5:int128) (a6:int128).
     aligned 16 (word_add kptr (word 32))
     ==> ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x120) /\
            read RCX s = kptr /\
            read (memory :> bytes128 (word_add kptr (word 32))) s = kq1 /\
            read (memory :> bytes128 (word_add kptr (word 64))) s = kq2 /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (\s. read RIP s = word (pc + 0x14d) /\
            read RCX s = kptr /\
            read (memory :> bytes128 (word_add kptr (word 64))) s = kq2 /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (CR4 l (simd4 word_add kq1 a4)))
                        (EL 3 (CR4 l (simd4 word_add kq1 a4)))
                        (EL 6 (CR4 l (simd4 word_add kq1 a4)))
                        (EL 7 (CR4 l (simd4 word_add kq1 a4))) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (CR4 l (simd4 word_add kq1 a4)))
                        (EL 1 (CR4 l (simd4 word_add kq1 a4)))
                        (EL 4 (CR4 l (simd4 word_add kq1 a4)))
                        (EL 5 (CR4 l (simd4 word_add kq1 a4))) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = sha256_msg2 a5 a4 /\
            word_subword (read YMM6_SSE s) (0,128) =
              simd4 word_add a6
                (word_subword
                   (word_ushr
                      ((word_join:int128->int128->256 word) (sha256_msg2 a5 a4) a4)
                      (8 * 4)) (0,128)) /\
            word_subword (read YMM3_SSE s) (0,128) = sha256_msg1 a3 a4)
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM5_SSE; YMM6_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x129`
   `\s. read RCX s = kptr /\
        read (memory :> bytes128 (word_add kptr (word 64))) s = kq2 /\
        word_subword (read YMM0_SSE s) (0,128) = simd4 word_add kq1 a4 /\
        word_subword (read YMM1_SSE s) (0,128) =
          ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
        word_subword (read YMM2_SSE s) (0,128) =
          CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
        word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
        word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
        word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
        word_subword (read YMM6_SSE s) (0,128) = (a6:int128)` THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
    REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC(REWRITE_RULE[SOME_FLAGS]
        SHA256_COMPRESS_HW_GROUP_STEP4_SM_R1_PACKED)]);;

Printf.printf "SHA256_COMPRESS_HW Phase-4 strengthened full-group seam atom (r=1) PROVEN.\n%!";;

(* ------------------------------------------------------------------------- *)
(* Phase-4 multi-group composition (session 036).                            *)
(*                                                                           *)
(* ENSURES_SUBLEMMA_REFL_TAC: the reflexive-seam variant of                  *)
(* ENSURES_SUBLEMMA_TAC (common/relational.ml:2362).  The stock tactic       *)
(* assumes a 3-conjunct shape after MATCH_MP_TAC ENSURES_SUBLEMMA_THM +       *)
(* REWRITE_TAC[]: (!s. P s ==> P' s) /\ R' subsumed R /\ (!s s'. ...).  When  *)
(* the seam predicate Q is stated to be EXACTLY the sub-lemma's instantiated  *)
(* precondition (every seam in the 16-group chain is reflexive by            *)
(* construction), the leading conjunct beta-reduces to `!s. body ==> body`,  *)
(* which the internal REWRITE_TAC[] collapses to T and DELETES, leaving only  *)
(* 2 conjuncts.  The stock CONJ_TAC then applies its P==>P' branch            *)
(* (X_GEN_TAC ... STRIP_TAC) to the `subsumed` goal whose head is not `!`,    *)
(* and dest_binder raises Failure.  ENSURES_SUBLEMMA_REFL_TAC is the stock    *)
(* tactic's SECOND branch alone -- exactly what survives the collapse.        *)
(* Diagnosed + verified on the live server by the s035 advisor; see           *)
(* orchestrator/logs/session-035-advisor.md.                                  *)
(* ------------------------------------------------------------------------- *)

let ENSURES_SUBLEMMA_REFL_TAC execth s0 s1 =
  MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN REWRITE_TAC[] THEN
  CONJ_TAC THENL [SUBSUMED_MAYCHANGE_TAC THEN NO_TAC; ALL_TAC] THEN
  W(fun (asl,w) -> X_GEN_TAC(mk_var(s0,type_of(fst(dest_forall w))))) THEN
  W(fun (asl,w) -> X_GEN_TAC(mk_var(s1,type_of(fst(dest_forall w))))) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
  REWRITE_TAC[GSYM SEQ_ASSOC] THEN
  PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
  CONV_TAC (TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[ASSIGNS_THM] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
  NONSELFMODIFYING_STATE_UPDATE_TAC execth THEN
  ASSUMPTION_STATE_UPDATE_TAC THEN DISCH_THEN(K ALL_TAC);;

let execup = MATCH_MP bytes_loaded_update (fst SHA256_COMPRESS_HW_EXEC);;

(* ------------------------------------------------------------------------- *)
(* THE 2-GROUP COMPOSITION.  g4 (r=0) ⨾ g5 (r=1) composed at the K-load seam  *)
(* pc+0x120 (pc+0xf4 -> pc+0x14d), exercising the real group-to-group seam:   *)
(*   - crypto accumulator: xmm1/xmm2 = ABEF/CDGH_PACK(CR4 l wk0) after g4      *)
(*     feed g5 as its ABEF/CDGH input -> CR4 (CR4 l wk0) wk1;                  *)
(*   - message ring: g4's post ring regs (incl the in-flight YMM5 partial)    *)
(*     become g5's ring inputs;                                               *)
(*   - the K pointer RCX threads both K-loads (g4 reads [rcx], g5 [rcx+0x20]). *)
(* Leg 1 uses the stock ENSURES_SUBLEMMA_TAC (its composed pre carries an     *)
(* extra kq2 conjunct FULL_S's pre lacks, so P==>P' is non-trivial and the    *)
(* 3-conjunct shape holds); leg 2's seam is reflexive, so it uses             *)
(* ENSURES_SUBLEMMA_REFL_TAC.  The (a5:int128) annotation on the seam Q is    *)
(* required: simd4's result width is not pinned by word_subword _ (0,128), so *)
(* a bare a5 there parses with a free type var distinct from the binder a5.   *)
(* ------------------------------------------------------------------------- *)

let SHA256_COMPRESS_HW_CORE_2GROUP = prove
 (`!pc kbase (kptr:int64) (l:int32 list) (kq0:int128) (kq1:int128) (kq2:int128)
      (a3:int128) (a4:int128) (a5:int128) (a6:int128).
     aligned 16 kptr
     ==> ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0xf4) /\
            read RCX s = kptr /\
            read (memory :> bytes128 kptr) s = kq0 /\
            read (memory :> bytes128 (word_add kptr (word 32))) s = kq1 /\
            read (memory :> bytes128 (word_add kptr (word 64))) s = kq2 /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (\s. read RIP s = word (pc + 0x14d) /\
            read RCX s = kptr /\
            read (memory :> bytes128 (word_add kptr (word 64))) s = kq2 /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK
                (EL 2 (CR4 (CR4 l (simd4 word_add kq0 a3)) (simd4 word_add kq1 (sha256_msg2 a4 a3))))
                (EL 3 (CR4 (CR4 l (simd4 word_add kq0 a3)) (simd4 word_add kq1 (sha256_msg2 a4 a3))))
                (EL 6 (CR4 (CR4 l (simd4 word_add kq0 a3)) (simd4 word_add kq1 (sha256_msg2 a4 a3))))
                (EL 7 (CR4 (CR4 l (simd4 word_add kq0 a3)) (simd4 word_add kq1 (sha256_msg2 a4 a3)))) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK
                (EL 0 (CR4 (CR4 l (simd4 word_add kq0 a3)) (simd4 word_add kq1 (sha256_msg2 a4 a3))))
                (EL 1 (CR4 (CR4 l (simd4 word_add kq0 a3)) (simd4 word_add kq1 (sha256_msg2 a4 a3))))
                (EL 4 (CR4 (CR4 l (simd4 word_add kq0 a3)) (simd4 word_add kq1 (sha256_msg2 a4 a3))))
                (EL 5 (CR4 (CR4 l (simd4 word_add kq0 a3)) (simd4 word_add kq1 (sha256_msg2 a4 a3)))) /\
            word_subword (read YMM5_SSE s) (0,128) =
              sha256_msg2
                (simd4 word_add a5
                   (word_subword
                      (word_ushr
                         ((word_join:int128->int128->256 word) (sha256_msg2 a4 a3) a3)
                         (8 * 4)) (0,128)))
                (sha256_msg2 a4 a3) /\
            word_subword (read YMM6_SSE s) (0,128) =
              simd4 word_add (sha256_msg1 a6 a3)
                (word_subword
                   (word_ushr
                      ((word_join:int128->int128->256 word)
                         (sha256_msg2
                            (simd4 word_add a5
                               (word_subword
                                  (word_ushr
                                     ((word_join:int128->int128->256 word)
                                        (sha256_msg2 a4 a3) a3) (8 * 4)) (0,128)))
                            (sha256_msg2 a4 a3)) (sha256_msg2 a4 a3))
                      (8 * 4)) (0,128)) /\
            word_subword (read YMM3_SSE s) (0,128) =
              sha256_msg1 a3 (sha256_msg2 a4 a3))
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM5_SSE; YMM6_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `aligned 16 (word_add (kptr:int64) (word 32))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORMALIZE_ALIGNED_WORD_CONV
       `aligned 16 (word_add (kptr:int64) (word 32))`]; ALL_TAC] THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x120`
   `\s. read RCX s = kptr /\
        read (memory :> bytes128 (word_add kptr (word 32))) s = kq1 /\
        read (memory :> bytes128 (word_add kptr (word 64))) s = kq2 /\
        word_subword (read YMM1_SSE s) (0,128) =
          ABEF_PACK (EL 0 (CR4 l (simd4 word_add kq0 a3)))
                    (EL 1 (CR4 l (simd4 word_add kq0 a3)))
                    (EL 4 (CR4 l (simd4 word_add kq0 a3)))
                    (EL 5 (CR4 l (simd4 word_add kq0 a3))) /\
        word_subword (read YMM2_SSE s) (0,128) =
          CDGH_PACK (EL 2 (CR4 l (simd4 word_add kq0 a3)))
                    (EL 3 (CR4 l (simd4 word_add kq0 a3)))
                    (EL 6 (CR4 l (simd4 word_add kq0 a3)))
                    (EL 7 (CR4 l (simd4 word_add kq0 a3))) /\
        word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
        word_subword (read YMM4_SSE s) (0,128) = sha256_msg2 a4 a3 /\
        word_subword (read YMM5_SSE s) (0,128) =
          simd4 word_add (a5:int128)
            (word_subword
               (word_ushr
                  ((word_join:int128->int128->256 word) (sha256_msg2 a4 a3) a3)
                  (8 * 4)) (0,128)) /\
        word_subword (read YMM6_SSE s) (0,128) = sha256_msg1 a6 a3` THEN
  CONJ_TAC THENL
   [(* leg 1: group 4 (r=0) via FULL_S -- composed pre has an extra kq2         *)
    (* conjunct, so P==>P' is non-trivial and the stock 3-conjunct shape holds. *)
    MP_TAC(SPECL
      [`pc:num`; `kbase:num`; `kptr:int64`; `l:int32 list`;
       `kq0:int128`; `kq1:int128`; `a3:int128`; `a4:int128`;
       `a5:int128`; `a6:int128`]
      (REWRITE_RULE[SOME_FLAGS] SHA256_COMPRESS_HW_GROUP4_FULL_S)) THEN
    ASM_REWRITE_TAC[] THEN
    ENSURES_SUBLEMMA_TAC execup "s" "s'" THEN ASM_REWRITE_TAC[];
    (* leg 2: group 5 (r=1) via FULL_S_R1, ring inputs = g4's outputs.  Seam Q   *)
    (* == FULL_S_R1's instantiated pre exactly (reflexive) -> ENSURES_SUBLEMMA_  *)
    (* REFL_TAC.                                                                 *)
    MP_TAC(SPECL
      [`pc:num`; `kbase:num`; `kptr:int64`;
       `CR4 l (simd4 word_add kq0 a3) :int32 list`;
       `kq1:int128`; `kq2:int128`;
       `a3:int128`;
       `sha256_msg2 a4 a3 :int128`;
       `simd4 word_add a5
          (word_subword
             (word_ushr
                ((word_join:int128->int128->256 word) (sha256_msg2 a4 a3) a3)
                (8 * 4)) (0,128)) :int128`;
       `sha256_msg1 a6 a3 :int128`]
      (REWRITE_RULE[SOME_FLAGS] SHA256_COMPRESS_HW_GROUP4_FULL_S_R1)) THEN
    ASM_REWRITE_TAC[] THEN
    ENSURES_SUBLEMMA_REFL_TAC execup "s" "s'" THEN ASM_REWRITE_TAC[]]);;

Printf.printf "SHA256_COMPRESS_HW Phase-4 2-group composition (CORE_2GROUP) PROVEN, hyps=%d.\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_CORE_2GROUP));;

(* ------------------------------------------------------------------------- *)
(* WQUAD-instantiation corollary (session 036): the schedule-window semantic  *)
(* seam of the 2-group composition.  CORE_2GROUP's completed message register *)
(* post (YMM5') is the abstract term                                          *)
(*   sha256_msg2 (simd4 word_add a5 (palignr (sha256_msg2 a4 a3) a3))         *)
(*               (sha256_msg2 a4 a3).                                          *)
(* Under the natural ring instantiation for a steady group at schedule offset *)
(* n --                                                                       *)
(*   a3 := WQUAD W(n+8)..W(n+11)   (the held complete window),                *)
(*   a5 := sha256_msg1 (WQUAD W(n)..W(n+3)) (WQUAD W(n+4)..W(n+7))            *)
(*         (the msg1 partial from two groups back),                           *)
(*   sha256_msg2 a4 a3 := WQUAD W(n+12)..W(n+15)  (the previous group's        *)
(*         completed window; the staggered-pipeline inductive fact, carried    *)
(*         here as the hypothesis) --                                          *)
(* this LHS is aconv to WRING_STEP's LHS, so it rewrites to WQUAD             *)
(* W(n+16)..W(n+19).  (The LHS = CORE_2GROUP's YMM5' post with those bindings, *)
(* verified aconv separately -- so this is the actual 2-group post            *)
(* specialized, not a re-statement of WRING_STEP.)  This is the               *)
(* invariant-shaping step for the pending 16-group loop: the ring holds       *)
(* schedule windows, and each steady group completes the next via WRING_STEP  *)
(* with NO atom restructuring -- the seam is an instantiation, not a re-proof. *)
(* ------------------------------------------------------------------------- *)

let SHA256_HW_WRING_2GROUP_COROLLARY = prove
 (`!(m:int32 list) n (a4:int128).
     sha256_msg2 a4
        (WQUAD (sha256_msg_schedule m (n+8)) (sha256_msg_schedule m (n+9))
               (sha256_msg_schedule m (n+10)) (sha256_msg_schedule m (n+11)))
     = WQUAD (sha256_msg_schedule m (n+12)) (sha256_msg_schedule m (n+13))
             (sha256_msg_schedule m (n+14)) (sha256_msg_schedule m (n+15))
     ==>
     sha256_msg2
       (simd4 word_add
          (sha256_msg1
             (WQUAD (sha256_msg_schedule m n) (sha256_msg_schedule m (n+1))
                    (sha256_msg_schedule m (n+2)) (sha256_msg_schedule m (n+3)))
             (WQUAD (sha256_msg_schedule m (n+4)) (sha256_msg_schedule m (n+5))
                    (sha256_msg_schedule m (n+6)) (sha256_msg_schedule m (n+7))))
          (word_subword
             (word_ushr
                ((word_join:int128->int128->256 word)
                   (sha256_msg2 a4
                      (WQUAD (sha256_msg_schedule m (n+8)) (sha256_msg_schedule m (n+9))
                             (sha256_msg_schedule m (n+10)) (sha256_msg_schedule m (n+11))))
                   (WQUAD (sha256_msg_schedule m (n+8)) (sha256_msg_schedule m (n+9))
                          (sha256_msg_schedule m (n+10)) (sha256_msg_schedule m (n+11))))
                (8 * 4))
             (0,128)))
       (sha256_msg2 a4
          (WQUAD (sha256_msg_schedule m (n+8)) (sha256_msg_schedule m (n+9))
                 (sha256_msg_schedule m (n+10)) (sha256_msg_schedule m (n+11))))
     = WQUAD (sha256_msg_schedule m (n+16)) (sha256_msg_schedule m (n+17))
             (sha256_msg_schedule m (n+18)) (sha256_msg_schedule m (n+19))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MATCH_ACCEPT_TAC WRING_STEP);;

Printf.printf "SHA256_COMPRESS_HW Phase-4 WQUAD 2-group semantic seam corollary PROVEN, hyps=%d.\n%!"
  (List.length (hyp SHA256_HW_WRING_2GROUP_COROLLARY));;

(* Session 036 Task 4: the r=2 rotation of the strengthened seam atoms.          *)
(* Mechanical port of the committed r=1 atoms (SM_R1 / SM_R1_PACKED /             *)
(* FULL_S_R1).  Register rotation period-4: r=2 has held xmm5, msg2 xmm6,         *)
(* paddd (in-flight) xmm3, msg1 xmm4.  Step entry pc+0x156, exit pc+0x17a; the    *)
(* full group's K-load is at pc+0x14d = movdqa xmm0,[rcx+0x40]; paddd xmm0,xmm5.  *)
(* These + r=3 (SCHED_GROUP rotation) complete the 4 rotations the 16-group       *)
(* monolith chains.                                                              *)


(* ---- r=2 memory-threaded strengthened step (entry pc+0x156, exit 0x17a) ---- *)
(* r=2 roles: held xmm5, msg2 xmm6, paddd xmm3, msg1 xmm4.  YMM3 gets the        *)
(* in-flight paddd partial: YMM3' = simd4 word_add a3 (palignr (msg2 a6 a5) a5). *)
let SHA256_COMPRESS_HW_GROUP_STEP4_SM_R2 = prove
 (`!pc kbase (kptr:int64) mloc (mval:int128) wk abef cdgh (a3:int128) (a4:int128) (a5:int128) (a6:int128).
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x156) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) = (abef:int128) /\
            word_subword (read YMM2_SSE s) (0,128) = (cdgh:int128) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (\s. read RIP s = word (pc + 0x17a) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM2_SSE s) (0,128) = sha256_rnds2 cdgh abef wk /\
            word_subword (read YMM1_SSE s) (0,128) =
              sha256_rnds2 abef (sha256_rnds2 cdgh abef wk)
                           (word_subword wk (64,64) : int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = sha256_msg2 a6 a5 /\
            word_subword (read YMM3_SSE s) (0,128) =
              simd4 word_add a3
                (word_subword
                   (word_ushr
                      ((word_join:int128->int128->256 word) (sha256_msg2 a6 a5) a5)
                      (8 * 4)) (0,128)) /\
            word_subword (read YMM4_SSE s) (0,128) = sha256_msg1 a4 a5)
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM6_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s5" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s6" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s7" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s8" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s9" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC SHA256_RNDS2_WK_CONG THEN CONJ_TAC THEN
      CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC) THEN
  TRY REFL_TAC);;

Printf.printf "S036_STEP_SM_R2 hyps=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_GROUP_STEP4_SM_R2));;

let SHA256_COMPRESS_HW_GROUP_STEP4_SM_R2_PACKED = prove
 (`!pc kbase (kptr:int64) mloc (mval:int128) (l:int32 list) (wk:int128) (a3:int128) (a4:int128) (a5:int128) (a6:int128).
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x156) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (\s. read RIP s = word (pc + 0x17a) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (CR4 l wk)) (EL 3 (CR4 l wk))
                        (EL 6 (CR4 l wk)) (EL 7 (CR4 l wk)) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (CR4 l wk)) (EL 1 (CR4 l wk))
                        (EL 4 (CR4 l wk)) (EL 5 (CR4 l wk)) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = sha256_msg2 a6 a5 /\
            word_subword (read YMM3_SSE s) (0,128) =
              simd4 word_add a3
                (word_subword
                   (word_ushr
                      ((word_join:int128->int128->256 word) (sha256_msg2 a6 a5) a5)
                      (8 * 4)) (0,128)) /\
            word_subword (read YMM4_SSE s) (0,128) = sha256_msg1 a4 a5)
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM6_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  let GA = CONV_RULE(TOP_DEPTH_CONV let_CONV)
             (SPECL [`l:int32 list`; `wk:int128`] SHA256_RNDS2_GROUP_ADVANCE) in
  let GA1 = CONJUNCT1 GA and GA2 = CONJUNCT2 GA in
  let ATCF = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`l:int32 list`;
             `word_subword wk (0,32):int32`; `word_subword wk (32,32):int32`;
             `word_subword wk (64,32):int32`; `word_subword wk (96,32):int32`]
            ABEF_TWO_IS_CDGH_FOUR) in
  REPEAT GEN_TAC THEN REWRITE_TAC[CR4] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA2] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM ATCF] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA1] THEN
  MATCH_ACCEPT_TAC SHA256_COMPRESS_HW_GROUP_STEP4_SM_R2);;

Printf.printf "S036_STEP_SM_R2_PACKED hyps=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_GROUP_STEP4_SM_R2_PACKED));;

(* ---- r=2 full-group seam atom: K-load[rcx+0x40]+xmm5 then step_R2 ---------- *)
(* g6 K-load: pc+0x14d movdqa xmm0,[rcx+0x40]; pc+0x152 paddd xmm0,xmm5.         *)
(* Entry pc+0x14d, exit pc+0x17a.  wk = simd4 word_add kq2 a5 (a5 = held xmm5).  *)
(* Threads RCX + the next-next K quad (mem @ rcx+0x60) for a further group.      *)
let SHA256_COMPRESS_HW_GROUP4_FULL_S_R2 = prove
 (`!pc kbase (kptr:int64) (l:int32 list) (kq2:int128) (kq3:int128) (a3:int128) (a4:int128) (a5:int128) (a6:int128).
     aligned 16 (word_add kptr (word 64))
     ==> ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x14d) /\
            read RCX s = kptr /\
            read (memory :> bytes128 (word_add kptr (word 64))) s = kq2 /\
            read (memory :> bytes128 (word_add kptr (word 96))) s = kq3 /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (\s. read RIP s = word (pc + 0x17a) /\
            read RCX s = kptr /\
            read (memory :> bytes128 (word_add kptr (word 96))) s = kq3 /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (CR4 l (simd4 word_add kq2 a5)))
                        (EL 3 (CR4 l (simd4 word_add kq2 a5)))
                        (EL 6 (CR4 l (simd4 word_add kq2 a5)))
                        (EL 7 (CR4 l (simd4 word_add kq2 a5))) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (CR4 l (simd4 word_add kq2 a5)))
                        (EL 1 (CR4 l (simd4 word_add kq2 a5)))
                        (EL 4 (CR4 l (simd4 word_add kq2 a5)))
                        (EL 5 (CR4 l (simd4 word_add kq2 a5))) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = sha256_msg2 a6 a5 /\
            word_subword (read YMM3_SSE s) (0,128) =
              simd4 word_add a3
                (word_subword
                   (word_ushr
                      ((word_join:int128->int128->256 word) (sha256_msg2 a6 a5) a5)
                      (8 * 4)) (0,128)) /\
            word_subword (read YMM4_SSE s) (0,128) = sha256_msg1 a4 a5)
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM6_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x156`
   `\s. read RCX s = kptr /\
        read (memory :> bytes128 (word_add kptr (word 96))) s = kq3 /\
        word_subword (read YMM0_SSE s) (0,128) = simd4 word_add kq2 a5 /\
        word_subword (read YMM1_SSE s) (0,128) =
          ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
        word_subword (read YMM2_SSE s) (0,128) =
          CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
        word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
        word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
        word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
        word_subword (read YMM6_SSE s) (0,128) = (a6:int128)` THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
    REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC(REWRITE_RULE[SOME_FLAGS]
        SHA256_COMPRESS_HW_GROUP_STEP4_SM_R2_PACKED)]);;

Printf.printf "S036_FULL_S_R2 hyps=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_GROUP4_FULL_S_R2));;

(* ------------------------------------------------------------------------- *)
(* Phase-4 THREE-group composition (session 037).                            *)
(*                                                                           *)
(* g4 (r=0) ⨾ g5 (r=1) ⨾ g6 (r=2), pc+0xf4 -> pc+0x17a, seams @0x120,0x14d.  *)
(* This closes the s036 leg-2 kq3-drop blocker and, more importantly,        *)
(* validates the READ-ONLY K-QUAD FRAME-CARRY shape the 16-cut invariant     *)
(* needs.                                                                    *)
(*                                                                           *)
(* THE FIX (segment-composition.md "read-only facts ride the frame"):        *)
(* each FULL_S_Rn atom's pre reads TWO K quads (the one it consumes + the    *)
(* next) but its post threads only the NEXT one, DROPPING the two-ahead      *)
(* quad.  s036 built seamQ1 = g5's pre = {kq1,kq2}, which lacks the kq3      *)
(* (@kptr+96) that seamQ2 = g6's pre demands.  g5's relational leg           *)
(* (ASSUMPTION_STATE_UPDATE_TAC) only threads read-only facts present in its *)
(* precondition, so kq3 was unavailable and the reflexive leg left it        *)
(* unsolved.  Fix: seamQ1 CARRIES kq3 (@kptr+96) as well -- kq3 then rides   *)
(* g5's memory-free frame (memory not in g5's MAYCHANGE) pre->post, EXACTLY  *)
(* as CORE_2GROUP leg-1 already carries kq2 through g4.  Consequence: leg-2a *)
(* (g5) becomes NON-reflexive (seamQ1 strictly extends g5.pre by kq3) so it  *)
(* uses the STOCK ENSURES_SUBLEMMA_TAC; only leg-2b (g6, the terminal group) *)
(* is reflexive.  Every non-terminal group in the 16-chain drops precisely   *)
(* its two-ahead K quad, so the 16-cut invariant must carry the window of    *)
(* not-yet-consumed K quads on the read-only channel -- NOT thread K quads   *)
(* one-by-one through group posts.  Built programmatically (nohw            *)
(* SHA256_BLOCK_NOHW_BODY15_ROUND31 term-surgery pattern).                   *)
(* ------------------------------------------------------------------------- *)

(* -- term plumbing -- *)
let strip_atom th =
  let bod = snd(strip_forall(concl th)) in
  let ens = if is_imp bod then snd(dest_imp bod) else bod in
  let l,c = dest_comb ens in
  let l2,q = dest_comb l in
  let _,p = dest_comb l2 in (p,q,c);;
let vbyname th n = find (fun v -> name_of v = n) (fst(strip_forall(concl th)));;
let conjs_of_lam q = let s,body = dest_abs q in s, conjuncts body;;
let rhs_of c = snd(dest_eq c);;
let contains s sub =
  let ls=String.length s and lsub=String.length sub in
  let rec go i = i+lsub<=ls && (String.sub s i lsub = sub || go(i+1)) in go 0;;
let ymm_rhs post nm =
  let _,cs = conjs_of_lam post in
  let hit = find (fun c -> is_eq c && contains (string_of_term(fst(dest_eq c))) nm) cs in
  rhs_of hit;;
let list_of_abef post =                 (* CR4 list feeding ABEF_PACK (EL 0 L').. *)
  let ymm1 = ymm_rhs post "YMM1_SSE" in
  rand(rand(rator(rator(rator ymm1))));;

(* ============================ g4 (FULL_S, r=0) ============================ *)
let vF = SHA256_COMPRESS_HW_GROUP4_FULL_S;;
let g4th = INST [`kq0:int128`, vbyname vF "kq"] (SPEC_ALL vF);;
let (pg4,qg4,cg4) = strip_atom g4th;;
let l'  = list_of_abef qg4
and a3' = ymm_rhs qg4 "YMM3_SSE"
and a4' = ymm_rhs qg4 "YMM4_SSE"
and a5' = ymm_rhs qg4 "YMM5_SSE"
and a6' = ymm_rhs qg4 "YMM6_SSE";;

(* ============================ g5 (FULL_S_R1, r=1) ========================= *)
let vR1 = SHA256_COMPRESS_HW_GROUP4_FULL_S_R1;;
let g5th = INST [ l', vbyname vR1 "l"; a3', vbyname vR1 "a3";
                  a4', vbyname vR1 "a4"; a5', vbyname vR1 "a5";
                  a6', vbyname vR1 "a6" ] (SPEC_ALL vR1);;
let (pg5,qg5,cg5) = strip_atom g5th;;
let l''  = list_of_abef qg5
and a3'' = ymm_rhs qg5 "YMM3_SSE"
and a4'' = ymm_rhs qg5 "YMM4_SSE"
and a5'' = ymm_rhs qg5 "YMM5_SSE"
and a6'' = ymm_rhs qg5 "YMM6_SSE";;

(* ============================ g6 (FULL_S_R2, r=2) ========================= *)
let vR2 = SHA256_COMPRESS_HW_GROUP4_FULL_S_R2;;
let g6th = INST [ l'', vbyname vR2 "l"; a3'', vbyname vR2 "a3";
                  a4'', vbyname vR2 "a4"; a5'', vbyname vR2 "a5";
                  a6'', vbyname vR2 "a6" ] (SPEC_ALL vR2);;
let (pg6,qg6,cg6) = strip_atom g6th;;

(* -- composed FRAME = all 8 YMM + RIP + flags + events -- *)
let full_frame =
  `MAYCHANGE [RIP] ,,
   MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM5_SSE; YMM6_SSE; YMM7_SSE] ,,
   MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;

(* -- composed PRE = g4's pre (@0xf4) + the two extra carried K reads kq2,kq3 -- *)
let svar = fst(dest_abs pg4);;
let _,pg4c = conjs_of_lam pg4;;
let sg6,pg6c = conjs_of_lam pg6;;
let is_kread nm c =
  is_eq c && contains (string_of_term c) "bytes128" && contains (string_of_term c) nm;;
let kq2read = vsubst[svar,sg6] (find (is_kread "64") pg6c)
and kq3read = vsubst[svar,sg6] (find (is_kread "96") pg6c);;
let pre_lam = mk_abs(svar, list_mk_conj (pg4c @ [kq2read; kq3read]));;

(* -- composed POST = g6's post (@0x17a) -- *)
let post_lam = qg6;;

(* -- build the composed ensures + hyps -- *)
let ens_head = rator(rator(rator(snd(dest_imp(snd(strip_forall(concl vF)))))));;
let mk_ensures p q c = mk_comb(mk_comb(mk_comb(ens_head,p),q),c);;
let bvars = [`pc:num`;`kbase:num`;`kptr:int64`;`l:int32 list`;
             `kq0:int128`;`kq1:int128`;`kq2:int128`;`kq3:int128`;
             `a3:int128`;`a4:int128`;`a5:int128`;`a6:int128`];;
let hyps = `aligned 16 (kptr:int64)`;;
let comp_concl = list_mk_forall(bvars, mk_imp(hyps, mk_ensures pre_lam post_lam full_frame));;

(* -- seam Q2 (@0x14d) = g6's instantiated PRE minus bytes_loaded + RIP -- *)
let seam_of pre =
  let s,cs = conjs_of_lam pre in
  let keep c = not(contains (string_of_term c) "bytes_loaded")
               && not(contains (string_of_term c) "read RIP") in
  mk_abs(s, list_mk_conj (filter keep cs));;
let seamQ2 = seam_of pg6;;

(* -- seam Q1 (@0x120) = g5's instantiated PRE minus bytes_loaded+RIP, PLUS the *)
(*    two-ahead kq3 read (kptr+96) that must survive g5 to feed g6 (leg-2b).    *)
(*    THE FIX vs s036: seamQ1 now carries kq3, so g5's leg is non-reflexive.    *)
let seamQ1 =
  let s,cs = conjs_of_lam pg5 in
  let keep c = not(contains (string_of_term c) "bytes_loaded")
               && not(contains (string_of_term c) "read RIP") in
  let kq3_for_s = vsubst[s,sg6] (find (is_kread "96") pg6c) in
  mk_abs(s, list_mk_conj (filter keep cs @ [kq3_for_s]));;

(* ------------------------------ THE PROOF ------------------------------ *)
let SHA256_COMPRESS_HW_CORE_3GROUP = prove
 (comp_concl,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `aligned 16 (word_add (kptr:int64) (word 32))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORMALIZE_ALIGNED_WORD_CONV
       `aligned 16 (word_add (kptr:int64) (word 32))`]; ALL_TAC] THEN
  SUBGOAL_THEN `aligned 16 (word_add (kptr:int64) (word 64))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORMALIZE_ALIGNED_WORD_CONV
       `aligned 16 (word_add (kptr:int64) (word 64))`]; ALL_TAC] THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x120` seamQ1 THEN CONJ_TAC THENL
   [(* leg 1: g4 -- composed pre carries extra kq2,kq3 -> non-reflexive -> stock *)
    MP_TAC(REWRITE_RULE[SOME_FLAGS] g4th) THEN ASM_REWRITE_TAC[] THEN
    ENSURES_SUBLEMMA_TAC execup "s" "s'" THEN ASM_REWRITE_TAC[];
    (* remaining: g5 ⨾ g6, seam @0x14d *)
    ENSURES_SEQUENCE_TAC `pc + 0x14d` seamQ2 THEN CONJ_TAC THENL
     [(* leg 2a: g5 -- seamQ1 carries kq3 beyond g5.pre -> NON-reflexive -> stock *)
      MP_TAC(REWRITE_RULE[SOME_FLAGS] g5th) THEN ASM_REWRITE_TAC[] THEN
      ENSURES_SUBLEMMA_TAC execup "s" "s'" THEN ASM_REWRITE_TAC[];
      (* leg 2b: g6 -- seamQ2 == g6.pre exactly, composed POST == g6.post -> refl *)
      MP_TAC(REWRITE_RULE[SOME_FLAGS] g6th) THEN ASM_REWRITE_TAC[] THEN
      ENSURES_SUBLEMMA_REFL_TAC execup "s" "s'" THEN ASM_REWRITE_TAC[]]]);;

Printf.printf "S037_CORE_3GROUP hyps=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_CORE_3GROUP));;
(* Session 037 Task 2: the r=3 rotation of the strengthened seam atoms.          *)
(* Mechanical port of the committed r=2 atoms (SM_R2 / SM_R2_PACKED / FULL_S_R2). *)
(* Register rotation period-4: r=3 has held xmm6, msg2 xmm3, paddd (in-flight)    *)
(* xmm4, msg1 xmm5.  YMM4 gets the in-flight paddd partial.                        *)
(* PCs verified vs objdump (proof-PC = file-offset - 4):                          *)
(*   K-load  file 0x17e movdqa xmm0,[rcx+0x60] -> proof pc+0x17a; paddd xmm0,xmm6. *)
(*   SM step file 0x187 sha256msg2 xmm3,xmm6   -> proof pc+0x183 (entry).          *)
(*   exit    file 0x1ab movdqa xmm0,[rcx+0x80] -> proof pc+0x1a7 (= next K-load).  *)
(* These complete the 4 period-4 rotations of the strengthened full-group atom.   *)


(* ---- r=3 memory-threaded strengthened step (entry pc+0x183, exit 0x1a7) ---- *)
(* r=3 roles: held xmm6, msg2 xmm3, paddd xmm4, msg1 xmm5.  YMM4' = in-flight    *)
(* paddd partial = simd4 word_add a4 (palignr (msg2 a3 a6) a6).                   *)
let SHA256_COMPRESS_HW_GROUP_STEP4_SM_R3 = prove
 (`!pc kbase (kptr:int64) mloc (mval:int128) wk abef cdgh (a3:int128) (a4:int128) (a5:int128) (a6:int128).
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x183) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) = (abef:int128) /\
            word_subword (read YMM2_SSE s) (0,128) = (cdgh:int128) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (\s. read RIP s = word (pc + 0x1a7) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM2_SSE s) (0,128) = sha256_rnds2 cdgh abef wk /\
            word_subword (read YMM1_SSE s) (0,128) =
              sha256_rnds2 abef (sha256_rnds2 cdgh abef wk)
                           (word_subword wk (64,64) : int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128) /\
            word_subword (read YMM3_SSE s) (0,128) = sha256_msg2 a3 a6 /\
            word_subword (read YMM4_SSE s) (0,128) =
              simd4 word_add a4
                (word_subword
                   (word_ushr
                      ((word_join:int128->int128->256 word) (sha256_msg2 a3 a6) a6)
                      (8 * 4)) (0,128)) /\
            word_subword (read YMM5_SSE s) (0,128) = sha256_msg1 a5 a6)
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM5_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s5" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s6" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s7" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s8" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s9" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC SHA256_RNDS2_WK_CONG THEN CONJ_TAC THEN
      CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC) THEN
  TRY REFL_TAC);;

Printf.printf "S037_STEP_SM_R3 hyps=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_GROUP_STEP4_SM_R3));;

let SHA256_COMPRESS_HW_GROUP_STEP4_SM_R3_PACKED = prove
 (`!pc kbase (kptr:int64) mloc (mval:int128) (l:int32 list) (wk:int128) (a3:int128) (a4:int128) (a5:int128) (a6:int128).
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x183) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (\s. read RIP s = word (pc + 0x1a7) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (CR4 l wk)) (EL 3 (CR4 l wk))
                        (EL 6 (CR4 l wk)) (EL 7 (CR4 l wk)) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (CR4 l wk)) (EL 1 (CR4 l wk))
                        (EL 4 (CR4 l wk)) (EL 5 (CR4 l wk)) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128) /\
            word_subword (read YMM3_SSE s) (0,128) = sha256_msg2 a3 a6 /\
            word_subword (read YMM4_SSE s) (0,128) =
              simd4 word_add a4
                (word_subword
                   (word_ushr
                      ((word_join:int128->int128->256 word) (sha256_msg2 a3 a6) a6)
                      (8 * 4)) (0,128)) /\
            word_subword (read YMM5_SSE s) (0,128) = sha256_msg1 a5 a6)
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM5_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  let GA = CONV_RULE(TOP_DEPTH_CONV let_CONV)
             (SPECL [`l:int32 list`; `wk:int128`] SHA256_RNDS2_GROUP_ADVANCE) in
  let GA1 = CONJUNCT1 GA and GA2 = CONJUNCT2 GA in
  let ATCF = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`l:int32 list`;
             `word_subword wk (0,32):int32`; `word_subword wk (32,32):int32`;
             `word_subword wk (64,32):int32`; `word_subword wk (96,32):int32`]
            ABEF_TWO_IS_CDGH_FOUR) in
  REPEAT GEN_TAC THEN REWRITE_TAC[CR4] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA2] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM ATCF] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA1] THEN
  MATCH_ACCEPT_TAC SHA256_COMPRESS_HW_GROUP_STEP4_SM_R3);;

Printf.printf "S037_STEP_SM_R3_PACKED hyps=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_GROUP_STEP4_SM_R3_PACKED));;

(* ---- r=3 full-group seam atom: K-load[rcx+0x60]+xmm6 then step_R3 ---------- *)
(* g7 K-load: pc+0x17a movdqa xmm0,[rcx+0x60]; pc+0x17f paddd xmm0,xmm6.          *)
(* Entry pc+0x17a, exit pc+0x1a7.  wk = simd4 word_add kq3 a6 (a6 = held xmm6).   *)
(* Threads RCX + the next-next K quad (mem @ rcx+0x80 = kptr+128) for a further   *)
(* group.                                                                        *)
let SHA256_COMPRESS_HW_GROUP4_FULL_S_R3 = prove
 (`!pc kbase (kptr:int64) (l:int32 list) (kq3:int128) (kq4:int128) (a3:int128) (a4:int128) (a5:int128) (a6:int128).
     aligned 16 (word_add kptr (word 96))
     ==> ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x17a) /\
            read RCX s = kptr /\
            read (memory :> bytes128 (word_add kptr (word 96))) s = kq3 /\
            read (memory :> bytes128 (word_add kptr (word 128))) s = kq4 /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (\s. read RIP s = word (pc + 0x1a7) /\
            read RCX s = kptr /\
            read (memory :> bytes128 (word_add kptr (word 128))) s = kq4 /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (CR4 l (simd4 word_add kq3 a6)))
                        (EL 3 (CR4 l (simd4 word_add kq3 a6)))
                        (EL 6 (CR4 l (simd4 word_add kq3 a6)))
                        (EL 7 (CR4 l (simd4 word_add kq3 a6))) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (CR4 l (simd4 word_add kq3 a6)))
                        (EL 1 (CR4 l (simd4 word_add kq3 a6)))
                        (EL 4 (CR4 l (simd4 word_add kq3 a6)))
                        (EL 5 (CR4 l (simd4 word_add kq3 a6))) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128) /\
            word_subword (read YMM3_SSE s) (0,128) = sha256_msg2 a3 a6 /\
            word_subword (read YMM4_SSE s) (0,128) =
              simd4 word_add a4
                (word_subword
                   (word_ushr
                      ((word_join:int128->int128->256 word) (sha256_msg2 a3 a6) a6)
                      (8 * 4)) (0,128)) /\
            word_subword (read YMM5_SSE s) (0,128) = sha256_msg1 a5 a6)
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM5_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x183`
   `\s. read RCX s = kptr /\
        read (memory :> bytes128 (word_add kptr (word 128))) s = kq4 /\
        word_subword (read YMM0_SSE s) (0,128) = simd4 word_add kq3 a6 /\
        word_subword (read YMM1_SSE s) (0,128) =
          ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
        word_subword (read YMM2_SSE s) (0,128) =
          CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
        word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
        word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
        word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
        word_subword (read YMM6_SSE s) (0,128) = (a6:int128)` THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
    REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC(REWRITE_RULE[SOME_FLAGS]
        SHA256_COMPRESS_HW_GROUP_STEP4_SM_R3_PACKED)]);;

Printf.printf "S037_FULL_S_R3 hyps=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_GROUP4_FULL_S_R3));;
Printf.printf "S037_R3_DONE\n%!";;

(* ------------------------------------------------------------------------- *)
(* Session 044 — the OPAQUE-ACCUMULATOR bridge (spec-threaded seam glue).      *)
(*                                                                           *)
(* The concrete-threading composers (CORE_2/3/4GROUP) thread each group's raw *)
(* CR4/msg1/msg2/simd4 POST occupants into the next group's ring binders; that *)
(* is EXPONENTIAL (3^groups, session 043).  The monolith instead threads the   *)
(* SPEC accumulators: crypto = ABEF/CDGH_PACK(EL k (compress_rounds m st (4g))) *)
(* and schedule ring = WQUAD windows of sha256_msg_schedule.  These two lemmas *)
(* fuse the K+W round-key into the crypto advance at the quad level.           *)
(*                                                                           *)
(* NB: never WORD_BLAST the join-reassociated int128 (simd4 is a balanced      *)
(* word_join, WQUAD is right-associated); reason at the lane-subword level      *)
(* (CR4 only ever reads word_subword wk (32j,32)), which reduces cheaply.      *)
(* ------------------------------------------------------------------------- *)

(* The four 32-bit lanes of `simd4 word_add (WQUAD ..)(WQUAD ..)` are the       *)
(* lane-wise word_adds — exactly the round-key words CR4 consumes.              *)
let SIMD4_ADD_WQUAD_SUBWORD = prove
 (`!a0 a1 a2 a3 b0 b1 b2 b3:int32.
     word_subword (simd4 word_add (WQUAD a0 a1 a2 a3) (WQUAD b0 b1 b2 b3)) (0,32)
       = word_add a0 b0 /\
     word_subword (simd4 word_add (WQUAD a0 a1 a2 a3) (WQUAD b0 b1 b2 b3)) (32,32)
       = word_add a1 b1 /\
     word_subword (simd4 word_add (WQUAD a0 a1 a2 a3) (WQUAD b0 b1 b2 b3)) (64,32)
       = word_add a2 b2 /\
     word_subword (simd4 word_add (WQUAD a0 a1 a2 a3) (WQUAD b0 b1 b2 b3)) (96,32)
       = word_add a3 b3`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simd4; simd2; WQUAD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[]);;

Printf.printf "SHA256_COMPRESS_HW S044 SIMD4_ADD_WQUAD_SUBWORD PROVEN.\n%!";;

(* THE CRYPTO HALF of the per-group SPEC-STEP: a group whose round-key register *)
(* is (K-window quad) simd4+ (W-window quad) advances the opaque compress state  *)
(* from 4g to 4g+4.  Discharges CR4_COMPRESS_STEP's four wk = K_t + W_t hyps.    *)
let CR4_SPEC_STEP = prove
 (`!(m:int32 list) (st:int32 list) n.
     CR4 (sha256_compress_rounds m st n)
         (simd4 word_add
            (WQUAD (EL n sha256_constants) (EL (n+1) sha256_constants)
                   (EL (n+2) sha256_constants) (EL (n+3) sha256_constants))
            (WQUAD (sha256_msg_schedule m n) (sha256_msg_schedule m (n+1))
                   (sha256_msg_schedule m (n+2)) (sha256_msg_schedule m (n+3))))
     = sha256_compress_rounds m st (n + 4)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC CR4_COMPRESS_STEP THEN
  REWRITE_TAC[SIMD4_ADD_WQUAD_SUBWORD]);;

Printf.printf "SHA256_COMPRESS_HW S044 CR4_SPEC_STEP PROVEN.\n%!";;

(* ------------------------------------------------------------------------- *)
(* The SCHEDULE-RING invariant, in opaque schedule-window form.               *)
(*                                                                           *)
(* WWIN m j     = the packed schedule window {W_j .. W_{j+3}}.                *)
(* MSG1P m j    = the msg1 partial  sha256_msg1 (WWIN j)(WWIN j+4).            *)
(* PADP m j     = MSG1P j after the palignr {W_{t-7}} paddd (the second stage *)
(*                of the staggered pipeline).                                 *)
(* At a steady r=0 group entry (o = 4g) the message ring xmm3..xmm6 holds      *)
(*   (WWIN o, PADP(o-12), MSG1P(o-8), WWIN(o-4)),                             *)
(* and one group step rotates it to the r=1 shape at o+4.  The only non-trivial*)
(* fold is xmm4' = sha256_msg2 (PADP(o-12)) (WWIN o) = WWIN(o+4) — i.e.        *)
(* WRING_STEP re-expressed over these abbreviations (WRING_WWIN).             *)
(* ------------------------------------------------------------------------- *)
let WWIN = new_definition
 `WWIN (m:int32 list) (j:num) : int128 =
    WQUAD (sha256_msg_schedule m j) (sha256_msg_schedule m (j+1))
          (sha256_msg_schedule m (j+2)) (sha256_msg_schedule m (j+3))`;;

let MSG1P = new_definition
 `MSG1P (m:int32 list) (j:num) : int128 = sha256_msg1 (WWIN m j) (WWIN m (j+4))`;;

let PADP = new_definition
 `PADP (m:int32 list) (j:num) : int128 =
    simd4 word_add (MSG1P m j)
      (word_subword
         (word_ushr ((word_join:int128->int128->256 word)
                        (WWIN m (j+12)) (WWIN m (j+8)))
                    (8 * 4)) (0,128))`;;

(* Flatten the nested (j+a)+b offsets that WWIN-unfolding produces to the flat  *)
(* j+(a+b) form WRING_STEP is stated in (segment-composition.md flat-vs-nested).*)
let S044_OFF_NORM = ARITH_RULE
 `((j + 4) + 1 = j + 5) /\ ((j + 4) + 2 = j + 6) /\ ((j + 4) + 3 = j + 7) /\
  ((j + 8) + 1 = j + 9) /\ ((j + 8) + 2 = j + 10) /\ ((j + 8) + 3 = j + 11) /\
  ((j + 12) + 1 = j + 13) /\ ((j + 12) + 2 = j + 14) /\ ((j + 12) + 3 = j + 15) /\
  ((j + 16) + 1 = j + 17) /\ ((j + 16) + 2 = j + 18) /\ ((j + 16) + 3 = j + 19)`;;

(* THE RING FOLD: msg2 (PADP j) (WWIN j+12) = WWIN j+16.  This is WRING_STEP.    *)
let WRING_WWIN = prove
 (`!(m:int32 list) j.
     sha256_msg2 (PADP m j) (WWIN m (j+12)) = WWIN m (j+16)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PADP; MSG1P; WWIN] THEN
  REWRITE_TAC[S044_OFF_NORM] THEN
  MP_TAC(SPECL [`m:int32 list`; `j:num`] WRING_STEP) THEN
  REWRITE_TAC[]);;

let MSG1_WWIN = prove
 (`!(m:int32 list) j. sha256_msg1 (WWIN m j) (WWIN m (j+4)) = MSG1P m j`,
  REWRITE_TAC[MSG1P]);;

Printf.printf "SHA256_COMPRESS_HW S044 schedule-ring algebra (WWIN/MSG1P/PADP/WRING_WWIN) PROVEN.\n%!";;

(* ------------------------------------------------------------------------- *)
(* THE PER-GROUP SPEC-STEP (r=0), the opaque-accumulator monolith seam.        *)
(*                                                                           *)
(* This is the lemma the 16-cut monolith threads: a steady r=0 group (entry    *)
(* pc+0xf4, exit pc+0x120) advances the OPAQUE crypto accumulator              *)
(* compress_rounds 4g -> 4g+4 and rotates the schedule ring one place, with a  *)
(* CONSTANT-size ensures (no CR4/msg1/msg2 nesting).  It is GROUP4_FULL_S with  *)
(* the abstract binders instantiated to schedule-window / compress_rounds       *)
(* forms and the raw-op POST folded via CR4_SPEC_STEP + the ring folds.  This   *)
(* is the s030 opaque-accumulator mandate that the concrete-threading route     *)
(* (CORE_2/3/4GROUP, exponential) dropped — see memory monolith-harvest.        *)
(*                                                                           *)
(* Crypto PRE/POST use CDGH before ABEF to match GROUP4_FULL_S's conjunct       *)
(* order (ACCEPT_TAC needs syntactic identity, and /\ is ordered).             *)
(* ------------------------------------------------------------------------- *)

(* Crypto advance in WWIN form. *)
let CR4_SPEC_STEP_WWIN = prove
 (`!(m:int32 list) (st:int32 list) g.
     CR4 (sha256_compress_rounds m st (4*g))
         (simd4 word_add
            (WQUAD (EL (4*g) sha256_constants) (EL (4*g+1) sha256_constants)
                   (EL (4*g+2) sha256_constants) (EL (4*g+3) sha256_constants))
            (WWIN m (4*g)))
     = sha256_compress_rounds m st (4*g + 4)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WWIN] THEN
  MP_TAC(SPECL [`m:int32 list`; `st:int32 list`; `4*g:num`] CR4_SPEC_STEP) THEN
  REWRITE_TAC[ARITH_RULE `4*g+4 = (4*g)+4`]);;

(* Ring folds for the r=0 rotation at offset 4g (g>=3 gives the 4g-12 window).  *)
let R0_YMM4 = prove
 (`!(m:int32 list) g. 3 <= g ==>
     sha256_msg2 (PADP m (4*g-12)) (WWIN m (4*g)) = WWIN m (4*g+4)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`m:int32 list`; `4*g-12`] WRING_WWIN) THEN
  ASM_SIMP_TAC[ARITH_RULE `3 <= g ==> (4*g-12)+12 = 4*g`;
               ARITH_RULE `3 <= g ==> (4*g-12)+16 = 4*g+4`]);;

let R0_YMM6 = prove
 (`!(m:int32 list) g. 1 <= g ==>
     sha256_msg1 (WWIN m (4*g-4)) (WWIN m (4*g)) = MSG1P m (4*g-4)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MSG1P] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let R0_YMM5 = prove
 (`!(m:int32 list) g. 2 <= g ==>
     simd4 word_add (MSG1P m (4*g-8))
       (word_subword
          (word_ushr ((word_join:int128->int128->256 word)
                         (WWIN m (4*g+4)) (WWIN m (4*g)))
                     (8 * 4)) (0,128))
     = PADP m (4*g-8)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PADP] THEN
  ASM_SIMP_TAC[ARITH_RULE `2 <= g ==> (4*g-8)+12 = 4*g+4`;
               ARITH_RULE `2 <= g ==> (4*g-8)+8 = 4*g`]);;

let SHA256_COMPRESS_HW_SPEC_STEP_R0 = prove
 (`!pc kbase (kptr:int64) (m:int32 list) (st:int32 list) g (kq1:int128).
     aligned 16 kptr /\ 3 <= g
     ==> ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0xf4) /\
            read RCX s = kptr /\
            read (memory :> bytes128 kptr) s =
              WQUAD (EL (4*g) sha256_constants) (EL (4*g+1) sha256_constants)
                    (EL (4*g+2) sha256_constants) (EL (4*g+3) sha256_constants) /\
            read (memory :> bytes128 (word_add kptr (word 32))) s = kq1 /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (sha256_compress_rounds m st (4*g)))
                        (EL 1 (sha256_compress_rounds m st (4*g)))
                        (EL 4 (sha256_compress_rounds m st (4*g)))
                        (EL 5 (sha256_compress_rounds m st (4*g))) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (sha256_compress_rounds m st (4*g)))
                        (EL 3 (sha256_compress_rounds m st (4*g)))
                        (EL 6 (sha256_compress_rounds m st (4*g)))
                        (EL 7 (sha256_compress_rounds m st (4*g))) /\
            word_subword (read YMM3_SSE s) (0,128) = WWIN m (4*g) /\
            word_subword (read YMM4_SSE s) (0,128) = PADP m (4*g-12) /\
            word_subword (read YMM5_SSE s) (0,128) = MSG1P m (4*g-8) /\
            word_subword (read YMM6_SSE s) (0,128) = WWIN m (4*g-4))
       (\s. read RIP s = word (pc + 0x120) /\
            read RCX s = kptr /\
            read (memory :> bytes128 (word_add kptr (word 32))) s = kq1 /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (sha256_compress_rounds m st (4*g+4)))
                        (EL 3 (sha256_compress_rounds m st (4*g+4)))
                        (EL 6 (sha256_compress_rounds m st (4*g+4)))
                        (EL 7 (sha256_compress_rounds m st (4*g+4))) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (sha256_compress_rounds m st (4*g+4)))
                        (EL 1 (sha256_compress_rounds m st (4*g+4)))
                        (EL 4 (sha256_compress_rounds m st (4*g+4)))
                        (EL 5 (sha256_compress_rounds m st (4*g+4))) /\
            word_subword (read YMM3_SSE s) (0,128) = WWIN m (4*g) /\
            word_subword (read YMM4_SSE s) (0,128) = WWIN m (4*g+4) /\
            word_subword (read YMM5_SSE s) (0,128) = PADP m (4*g-8) /\
            word_subword (read YMM6_SSE s) (0,128) = MSG1P m (4*g-4))
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM4_SSE; YMM5_SSE; YMM6_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`m:int32 list`; `g:num`] R0_YMM4) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`m:int32 list`; `g:num`] R0_YMM5) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`m:int32 list`; `g:num`] R0_YMM6) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(INST
    [ `WWIN m (4*g) : int128`, `a3:int128`;
      `PADP m (4*g - 12) : int128`, `a4:int128`;
      `MSG1P m (4*g - 8) : int128`, `a5:int128`;
      `WWIN m (4*g - 4) : int128`, `a6:int128`;
      `WQUAD (EL (4*g) sha256_constants) (EL (4*g+1) sha256_constants)
             (EL (4*g+2) sha256_constants) (EL (4*g+3) sha256_constants) : int128`,
        `kq:int128`;
      `sha256_compress_rounds m (st:int32 list) (4*g) : int32 list`, `l:int32 list` ]
    (SPEC_ALL SHA256_COMPRESS_HW_GROUP4_FULL_S)) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[CR4_SPEC_STEP_WWIN] THEN
  DISCH_THEN ACCEPT_TAC);;

Printf.printf "SHA256_COMPRESS_HW S044 per-group SPEC-STEP (r=0) PROVEN (opaque accumulator).\n%!";;

(* The r=1 rotation SPEC-STEP.  The fold lemmas R0_YMM4/5/6 + CR4_SPEC_STEP_WWIN  *)
(* are stated over schedule OFFSETS (not register names), so they apply VERBATIM;  *)
(* only the atom (FULL_S_R1), the PCs (0x120->0x14d), the consumed K read          *)
(* (@kptr+32) and the ring role rotation change.  Entry ring (YMM3,4,5,6) =        *)
(* (WWIN 4g-4, WWIN 4g, PADP 4g-12, MSG1P 4g-8) with a4 = wk-source.               *)
let SHA256_COMPRESS_HW_SPEC_STEP_R1 = prove
 (`!pc kbase (kptr:int64) (m:int32 list) (st:int32 list) g (kq2:int128).
     aligned 16 (word_add kptr (word 32)) /\ 3 <= g
     ==> ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x120) /\
            read RCX s = kptr /\
            read (memory :> bytes128 (word_add kptr (word 32))) s =
              WQUAD (EL (4*g) sha256_constants) (EL (4*g+1) sha256_constants)
                    (EL (4*g+2) sha256_constants) (EL (4*g+3) sha256_constants) /\
            read (memory :> bytes128 (word_add kptr (word 64))) s = kq2 /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (sha256_compress_rounds m st (4*g)))
                        (EL 1 (sha256_compress_rounds m st (4*g)))
                        (EL 4 (sha256_compress_rounds m st (4*g)))
                        (EL 5 (sha256_compress_rounds m st (4*g))) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (sha256_compress_rounds m st (4*g)))
                        (EL 3 (sha256_compress_rounds m st (4*g)))
                        (EL 6 (sha256_compress_rounds m st (4*g)))
                        (EL 7 (sha256_compress_rounds m st (4*g))) /\
            word_subword (read YMM3_SSE s) (0,128) = WWIN m (4*g-4) /\
            word_subword (read YMM4_SSE s) (0,128) = WWIN m (4*g) /\
            word_subword (read YMM5_SSE s) (0,128) = PADP m (4*g-12) /\
            word_subword (read YMM6_SSE s) (0,128) = MSG1P m (4*g-8))
       (\s. read RIP s = word (pc + 0x14d) /\
            read RCX s = kptr /\
            read (memory :> bytes128 (word_add kptr (word 64))) s = kq2 /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (sha256_compress_rounds m st (4*g+4)))
                        (EL 3 (sha256_compress_rounds m st (4*g+4)))
                        (EL 6 (sha256_compress_rounds m st (4*g+4)))
                        (EL 7 (sha256_compress_rounds m st (4*g+4))) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (sha256_compress_rounds m st (4*g+4)))
                        (EL 1 (sha256_compress_rounds m st (4*g+4)))
                        (EL 4 (sha256_compress_rounds m st (4*g+4)))
                        (EL 5 (sha256_compress_rounds m st (4*g+4))) /\
            word_subword (read YMM4_SSE s) (0,128) = WWIN m (4*g) /\
            word_subword (read YMM5_SSE s) (0,128) = WWIN m (4*g+4) /\
            word_subword (read YMM6_SSE s) (0,128) = PADP m (4*g-8) /\
            word_subword (read YMM3_SSE s) (0,128) = MSG1P m (4*g-4))
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM5_SSE; YMM6_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`m:int32 list`; `g:num`] R0_YMM4) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`m:int32 list`; `g:num`] R0_YMM5) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`m:int32 list`; `g:num`] R0_YMM6) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(INST
    [ `WWIN m (4*g - 4) : int128`, `a3:int128`;
      `WWIN m (4*g) : int128`, `a4:int128`;
      `PADP m (4*g - 12) : int128`, `a5:int128`;
      `MSG1P m (4*g - 8) : int128`, `a6:int128`;
      `WQUAD (EL (4*g) sha256_constants) (EL (4*g+1) sha256_constants)
             (EL (4*g+2) sha256_constants) (EL (4*g+3) sha256_constants) : int128`,
        `kq1:int128`;
      `sha256_compress_rounds m (st:int32 list) (4*g) : int32 list`, `l:int32 list` ]
    (SPEC_ALL SHA256_COMPRESS_HW_GROUP4_FULL_S_R1)) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[CR4_SPEC_STEP_WWIN] THEN
  DISCH_THEN ACCEPT_TAC);;

Printf.printf "SHA256_COMPRESS_HW S044 per-group SPEC-STEP (r=1) PROVEN.\n%!";;

(* The r=2 rotation SPEC-STEP.  pc 0x14d->0x17a, K consumed @kptr+64, wk-source =  *)
(* a5 (YMM5).  Entry ring (YMM3,4,5,6) = (MSG1P 4g-8, WWIN 4g-4, WWIN 4g, PADP      *)
(* 4g-12).  Same fold set applies verbatim.                                        *)
let SHA256_COMPRESS_HW_SPEC_STEP_R2 = prove
 (`!pc kbase (kptr:int64) (m:int32 list) (st:int32 list) g (kq3:int128).
     aligned 16 (word_add kptr (word 64)) /\ 3 <= g
     ==> ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x14d) /\
            read RCX s = kptr /\
            read (memory :> bytes128 (word_add kptr (word 64))) s =
              WQUAD (EL (4*g) sha256_constants) (EL (4*g+1) sha256_constants)
                    (EL (4*g+2) sha256_constants) (EL (4*g+3) sha256_constants) /\
            read (memory :> bytes128 (word_add kptr (word 96))) s = kq3 /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (sha256_compress_rounds m st (4*g)))
                        (EL 1 (sha256_compress_rounds m st (4*g)))
                        (EL 4 (sha256_compress_rounds m st (4*g)))
                        (EL 5 (sha256_compress_rounds m st (4*g))) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (sha256_compress_rounds m st (4*g)))
                        (EL 3 (sha256_compress_rounds m st (4*g)))
                        (EL 6 (sha256_compress_rounds m st (4*g)))
                        (EL 7 (sha256_compress_rounds m st (4*g))) /\
            word_subword (read YMM3_SSE s) (0,128) = MSG1P m (4*g-8) /\
            word_subword (read YMM4_SSE s) (0,128) = WWIN m (4*g-4) /\
            word_subword (read YMM5_SSE s) (0,128) = WWIN m (4*g) /\
            word_subword (read YMM6_SSE s) (0,128) = PADP m (4*g-12))
       (\s. read RIP s = word (pc + 0x17a) /\
            read RCX s = kptr /\
            read (memory :> bytes128 (word_add kptr (word 96))) s = kq3 /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (sha256_compress_rounds m st (4*g+4)))
                        (EL 3 (sha256_compress_rounds m st (4*g+4)))
                        (EL 6 (sha256_compress_rounds m st (4*g+4)))
                        (EL 7 (sha256_compress_rounds m st (4*g+4))) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (sha256_compress_rounds m st (4*g+4)))
                        (EL 1 (sha256_compress_rounds m st (4*g+4)))
                        (EL 4 (sha256_compress_rounds m st (4*g+4)))
                        (EL 5 (sha256_compress_rounds m st (4*g+4))) /\
            word_subword (read YMM5_SSE s) (0,128) = WWIN m (4*g) /\
            word_subword (read YMM6_SSE s) (0,128) = WWIN m (4*g+4) /\
            word_subword (read YMM3_SSE s) (0,128) = PADP m (4*g-8) /\
            word_subword (read YMM4_SSE s) (0,128) = MSG1P m (4*g-4))
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM6_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`m:int32 list`; `g:num`] R0_YMM4) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`m:int32 list`; `g:num`] R0_YMM5) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`m:int32 list`; `g:num`] R0_YMM6) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(INST
    [ `MSG1P m (4*g - 8) : int128`, `a3:int128`;
      `WWIN m (4*g - 4) : int128`, `a4:int128`;
      `WWIN m (4*g) : int128`, `a5:int128`;
      `PADP m (4*g - 12) : int128`, `a6:int128`;
      `WQUAD (EL (4*g) sha256_constants) (EL (4*g+1) sha256_constants)
             (EL (4*g+2) sha256_constants) (EL (4*g+3) sha256_constants) : int128`, `kq2:int128`;
      `sha256_compress_rounds m (st:int32 list) (4*g) : int32 list`, `l:int32 list` ]
    (SPEC_ALL SHA256_COMPRESS_HW_GROUP4_FULL_S_R2)) THEN
  ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[CR4_SPEC_STEP_WWIN] THEN DISCH_THEN ACCEPT_TAC);;

Printf.printf "SHA256_COMPRESS_HW S044 per-group SPEC-STEP (r=2) PROVEN.\n%!";;

(* The r=3 rotation SPEC-STEP.  pc 0x17a->0x1a7, K consumed @kptr+96, wk-source =  *)
(* a6 (YMM6).  Entry ring (YMM3,4,5,6) = (PADP 4g-12, MSG1P 4g-8, WWIN 4g-4,        *)
(* WWIN 4g).  Closing the period-4 cycle: POST is the r=0 shape at 4g+4.            *)
let SHA256_COMPRESS_HW_SPEC_STEP_R3 = prove
 (`!pc kbase (kptr:int64) (m:int32 list) (st:int32 list) g (kq4:int128).
     aligned 16 (word_add kptr (word 96)) /\ 3 <= g
     ==> ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x17a) /\
            read RCX s = kptr /\
            read (memory :> bytes128 (word_add kptr (word 96))) s =
              WQUAD (EL (4*g) sha256_constants) (EL (4*g+1) sha256_constants)
                    (EL (4*g+2) sha256_constants) (EL (4*g+3) sha256_constants) /\
            read (memory :> bytes128 (word_add kptr (word 128))) s = kq4 /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (sha256_compress_rounds m st (4*g)))
                        (EL 1 (sha256_compress_rounds m st (4*g)))
                        (EL 4 (sha256_compress_rounds m st (4*g)))
                        (EL 5 (sha256_compress_rounds m st (4*g))) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (sha256_compress_rounds m st (4*g)))
                        (EL 3 (sha256_compress_rounds m st (4*g)))
                        (EL 6 (sha256_compress_rounds m st (4*g)))
                        (EL 7 (sha256_compress_rounds m st (4*g))) /\
            word_subword (read YMM3_SSE s) (0,128) = PADP m (4*g-12) /\
            word_subword (read YMM4_SSE s) (0,128) = MSG1P m (4*g-8) /\
            word_subword (read YMM5_SSE s) (0,128) = WWIN m (4*g-4) /\
            word_subword (read YMM6_SSE s) (0,128) = WWIN m (4*g))
       (\s. read RIP s = word (pc + 0x1a7) /\
            read RCX s = kptr /\
            read (memory :> bytes128 (word_add kptr (word 128))) s = kq4 /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (sha256_compress_rounds m st (4*g+4)))
                        (EL 3 (sha256_compress_rounds m st (4*g+4)))
                        (EL 6 (sha256_compress_rounds m st (4*g+4)))
                        (EL 7 (sha256_compress_rounds m st (4*g+4))) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (sha256_compress_rounds m st (4*g+4)))
                        (EL 1 (sha256_compress_rounds m st (4*g+4)))
                        (EL 4 (sha256_compress_rounds m st (4*g+4)))
                        (EL 5 (sha256_compress_rounds m st (4*g+4))) /\
            word_subword (read YMM6_SSE s) (0,128) = WWIN m (4*g) /\
            word_subword (read YMM3_SSE s) (0,128) = WWIN m (4*g+4) /\
            word_subword (read YMM4_SSE s) (0,128) = PADP m (4*g-8) /\
            word_subword (read YMM5_SSE s) (0,128) = MSG1P m (4*g-4))
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM5_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`m:int32 list`; `g:num`] R0_YMM4) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`m:int32 list`; `g:num`] R0_YMM5) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`m:int32 list`; `g:num`] R0_YMM6) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(INST
    [ `PADP m (4*g - 12) : int128`, `a3:int128`;
      `MSG1P m (4*g - 8) : int128`, `a4:int128`;
      `WWIN m (4*g - 4) : int128`, `a5:int128`;
      `WWIN m (4*g) : int128`, `a6:int128`;
      `WQUAD (EL (4*g) sha256_constants) (EL (4*g+1) sha256_constants)
             (EL (4*g+2) sha256_constants) (EL (4*g+3) sha256_constants) : int128`, `kq3:int128`;
      `sha256_compress_rounds m (st:int32 list) (4*g) : int32 list`, `l:int32 list` ]
    (SPEC_ALL SHA256_COMPRESS_HW_GROUP4_FULL_S_R3)) THEN
  ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[CR4_SPEC_STEP_WWIN] THEN DISCH_THEN ACCEPT_TAC);;

Printf.printf "SHA256_COMPRESS_HW S044 per-group SPEC-STEP (r=3) PROVEN.\n%!";;

(* Session 037 Task 3: CORE_4GROUP — a FULL period-4 rotation cycle composed.    *)
(* g4(r0) ⨾ g5(r1) ⨾ g6(r2) ⨾ g7(r3), pc+0xf4 -> pc+0x1a7, seams @0x120,0x14d,   *)
(* 0x17a.  Generalizes CORE_3GROUP by one leg; validates the read-only K-quad     *)
(* window frame-carry across ALL FOUR rotations and a 5-quad carried window       *)
(* (kq0..kq4), the exact shape the 16-cut invariant folds.                        *)
(*                                                                               *)
(* THE GENERALIZED FRAME-CARRY (segment-composition.md "read-only facts ride the  *)
(* frame"): each FULL_S_Rn atom's pre reads TWO K quads (consumed + next) but its *)
(* post threads only the NEXT one.  The composed PRE carries the whole window     *)
(* kq0..kq4; each seam Qi = g(i+1)'s pre PLUS the not-yet-consumed two-ahead      *)
(* quads, which ride the memory-free frame through the intervening group.  Only   *)
(* the TERMINAL group (g7) has a reflexive seam (its pre already lists both its   *)
(* quads and nothing is carried beyond it); every non-terminal leg is             *)
(* non-reflexive -> STOCK ENSURES_SUBLEMMA_TAC.  This is the 16-fold pattern:     *)
(* carry the live K-quad window on the read-only channel, not one-by-one.         *)



(* -- term plumbing (same as CORE_3GROUP) -- *)
let strip_atom th =
  let bod = snd(strip_forall(concl th)) in
  let ens = if is_imp bod then snd(dest_imp bod) else bod in
  let l,c = dest_comb ens in
  let l2,q = dest_comb l in
  let _,p = dest_comb l2 in (p,q,c);;
let vbyname th n = find (fun v -> name_of v = n) (fst(strip_forall(concl th)));;
let conjs_of_lam q = let s,body = dest_abs q in s, conjuncts body;;
let rhs_of c = snd(dest_eq c);;
let contains s sub =
  let ls=String.length s and lsub=String.length sub in
  let rec go i = i+lsub<=ls && (String.sub s i lsub = sub || go(i+1)) in go 0;;
let ymm_rhs post nm =
  let _,cs = conjs_of_lam post in
  let hit = find (fun c -> is_eq c && contains (string_of_term(fst(dest_eq c))) nm) cs in
  rhs_of hit;;
let list_of_abef post =
  let ymm1 = ymm_rhs post "YMM1_SSE" in
  rand(rand(rator(rator(rator ymm1))));;
(* NB: match the precise "(word N)" offset substring, NOT bare N -- every K read *)
(* term literally contains "bytes128" which contains "128", so a bare-"128" match *)
(* would wrongly hit kq0/kq3.  "(word 128)" is unique to the @kptr+128 read.       *)
let is_kread off c =
  is_eq c && contains (string_of_term c) "bytes128"
          && contains (string_of_term c) ("(word " ^ off ^ ")");;

(* Instantiate one FULL_S_Rn atom's ring binders (l,a3,a4,a5,a6) to prev post.   *)
let inst_ring atomthm l_v a3_v a4_v a5_v a6_v =
  INST [ l_v,  vbyname atomthm "l";  a3_v, vbyname atomthm "a3";
         a4_v, vbyname atomthm "a4"; a5_v, vbyname atomthm "a5";
         a6_v, vbyname atomthm "a6" ] (SPEC_ALL atomthm);;
let post_ring q =
  (list_of_abef q, ymm_rhs q "YMM3_SSE", ymm_rhs q "YMM4_SSE",
   ymm_rhs q "YMM5_SSE", ymm_rhs q "YMM6_SSE");;

(* ---- g4 (FULL_S, r=0): kq0@kptr, kq1@kptr+32 ---- *)
let vF = SHA256_COMPRESS_HW_GROUP4_FULL_S;;
let g4th = INST [`kq0:int128`, vbyname vF "kq"] (SPEC_ALL vF);;
let (pg4,qg4,cg4) = strip_atom g4th;;
let (l4,a34,a44,a54,a64) = post_ring qg4;;

(* ---- g5 (FULL_S_R1, r=1): kq1@kptr+32, kq2@kptr+64 ---- *)
let g5th = inst_ring SHA256_COMPRESS_HW_GROUP4_FULL_S_R1 l4 a34 a44 a54 a64;;
let (pg5,qg5,cg5) = strip_atom g5th;;
let (l5,a35,a45,a55,a65) = post_ring qg5;;

(* ---- g6 (FULL_S_R2, r=2): kq2@kptr+64, kq3@kptr+96 ---- *)
let g6th = inst_ring SHA256_COMPRESS_HW_GROUP4_FULL_S_R2 l5 a35 a45 a55 a65;;
let (pg6,qg6,cg6) = strip_atom g6th;;
let (l6,a36,a46,a56,a66) = post_ring qg6;;

(* ---- g7 (FULL_S_R3, r=3): kq3@kptr+96, kq4@kptr+128 ---- *)
let g7th = inst_ring SHA256_COMPRESS_HW_GROUP4_FULL_S_R3 l6 a36 a46 a56 a66;;
let (pg7,qg7,cg7) = strip_atom g7th;;

(* -- the individual K-read conjuncts, canonical state var svar4 (g4's) -- *)
let svar4,pg4c = conjs_of_lam pg4;;
let sg5,pg5c = conjs_of_lam pg5;;
let sg6,pg6c = conjs_of_lam pg6;;
let sg7,pg7c = conjs_of_lam pg7;;
(* offset->read term, bound to a given state var *)
let kread_for s src_svar src_conjs off =
  vsubst[s,src_svar] (find (is_kread off) src_conjs);;

(* -- composed FRAME = all 8 YMM + RIP + flags + events -- *)
let full_frame =
  `MAYCHANGE [RIP] ,,
   MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM5_SSE; YMM6_SSE; YMM7_SSE] ,,
   MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;

(* -- composed PRE = g4's pre + the three not-yet-in-g4 K reads kq2,kq3,kq4 -- *)
let pre_extra = [ kread_for svar4 sg6 pg6c "64";   (* kq2 @kptr+64  from g6 pre *)
                  kread_for svar4 sg7 pg7c "96";   (* kq3 @kptr+96  from g7 pre *)
                  kread_for svar4 sg7 pg7c "128" ];; (* kq4 @kptr+128 from g7 pre *)
let pre_lam = mk_abs(svar4, list_mk_conj (pg4c @ pre_extra));;

(* -- composed POST = g7's post (@0x1a7) -- *)
let post_lam = qg7;;

(* -- build the composed ensures + hyps -- *)
let ens_head = rator(rator(rator(snd(dest_imp(snd(strip_forall(concl vF)))))));;
let mk_ensures p q c = mk_comb(mk_comb(mk_comb(ens_head,p),q),c);;
let bvars = [`pc:num`;`kbase:num`;`kptr:int64`;`l:int32 list`;
             `kq0:int128`;`kq1:int128`;`kq2:int128`;`kq3:int128`;`kq4:int128`;
             `a3:int128`;`a4:int128`;`a5:int128`;`a6:int128`];;
let hyps = `aligned 16 (kptr:int64)`;;
let comp_concl = list_mk_forall(bvars, mk_imp(hyps, mk_ensures pre_lam post_lam full_frame));;


(* -- seams: seamQi = g(i+1)'s pre (minus bytes_loaded+RIP) + carried tail -- *)
let seam_core pre =
  let s,cs = conjs_of_lam pre in
  let keep c = not(contains (string_of_term c) "bytes_loaded")
               && not(contains (string_of_term c) "read RIP") in
  (s, filter keep cs);;
(* seamQ1 @0x120 (before g5): g5.pre + {kq3@96, kq4@128} *)
let seamQ1 =
  let s,cs = seam_core pg5 in
  mk_abs(s, list_mk_conj (cs @ [kread_for s sg7 pg7c "96"; kread_for s sg7 pg7c "128"]));;
(* seamQ2 @0x14d (before g6): g6.pre + {kq4@128} *)
let seamQ2 =
  let s,cs = seam_core pg6 in
  mk_abs(s, list_mk_conj (cs @ [kread_for s sg7 pg7c "128"]));;
(* seamQ3 @0x17a (before g7): g7.pre exactly (reflexive) *)
let seamQ3 =
  let s,cs = seam_core pg7 in mk_abs(s, list_mk_conj cs);;


(* ------------------------------ THE PROOF ------------------------------ *)
let mk_align n =
  SUBGOAL_THEN (mk_comb(`aligned 16`, mk_comb(mk_comb(`word_add:int64->int64->int64`,`kptr:int64`), mk_comb(`word:num->int64`, mk_small_numeral n))))
    ASSUME_TAC;;

let SHA256_COMPRESS_HW_CORE_4GROUP = prove
 (comp_concl,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `aligned 16 (word_add (kptr:int64) (word 32))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORMALIZE_ALIGNED_WORD_CONV
       `aligned 16 (word_add (kptr:int64) (word 32))`]; ALL_TAC] THEN
  SUBGOAL_THEN `aligned 16 (word_add (kptr:int64) (word 64))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORMALIZE_ALIGNED_WORD_CONV
       `aligned 16 (word_add (kptr:int64) (word 64))`]; ALL_TAC] THEN
  SUBGOAL_THEN `aligned 16 (word_add (kptr:int64) (word 96))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORMALIZE_ALIGNED_WORD_CONV
       `aligned 16 (word_add (kptr:int64) (word 96))`]; ALL_TAC] THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x120` seamQ1 THEN CONJ_TAC THENL
   [(* leg 1: g4 -- composed pre carries kq2,kq3,kq4 beyond g4 -> non-reflexive *)
    MP_TAC(REWRITE_RULE[SOME_FLAGS] g4th) THEN ASM_REWRITE_TAC[] THEN
    ENSURES_SUBLEMMA_TAC execup "s" "s'" THEN ASM_REWRITE_TAC[];
    ENSURES_SEQUENCE_TAC `pc + 0x14d` seamQ2 THEN CONJ_TAC THENL
     [(* leg 2: g5 -- seamQ1 carries kq3,kq4 beyond g5 -> non-reflexive *)
      MP_TAC(REWRITE_RULE[SOME_FLAGS] g5th) THEN ASM_REWRITE_TAC[] THEN
      ENSURES_SUBLEMMA_TAC execup "s" "s'" THEN ASM_REWRITE_TAC[];
      ENSURES_SEQUENCE_TAC `pc + 0x17a` seamQ3 THEN CONJ_TAC THENL
       [(* leg 3: g6 -- seamQ2 carries kq4 beyond g6 -> non-reflexive *)
        MP_TAC(REWRITE_RULE[SOME_FLAGS] g6th) THEN ASM_REWRITE_TAC[] THEN
        ENSURES_SUBLEMMA_TAC execup "s" "s'" THEN ASM_REWRITE_TAC[];
        (* leg 4: g7 -- seamQ3 == g7.pre exactly, POST == g7.post -> reflexive *)
        MP_TAC(REWRITE_RULE[SOME_FLAGS] g7th) THEN ASM_REWRITE_TAC[] THEN
        ENSURES_SUBLEMMA_REFL_TAC execup "s" "s'" THEN ASM_REWRITE_TAC[]]]]);;

Printf.printf "S037_CORE_4GROUP hyps=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_CORE_4GROUP));;
Printf.printf "S037_CORE_4GROUP_DONE\n%!";;

(* ========================================================================= *)
(* Session 038 — Phase 4: PARAMETRIC STEADY-STATE GROUP GENERATOR + the      *)
(* disp32 steady groups g8..g12.                                             *)
(*                                                                           *)
(* THE PARAMETRIC LEAP (STATE Current Step / Continuation task 1).  The four *)
(* committed rotation atoms FULL_S_R{0,1,2,3} (+ SM_R{0,1,2,3}_PACKED) are   *)
(* the r = g mod 4 TEMPLATES for the steady-state round-engine body.  Every  *)
(* steady group 3..12 is byte-identical to its rotation template modulo (a)  *)
(* the K-load displacement ENCODING LENGTH (disp0=4B g4; disp8=5B g3,g5,g6,  *)
(* g7; disp32=8B g8..g15) which shifts the internal PCs, and (b) the period-4 *)
(* register rotation.  So a group's SM_raw / SM_packed / FULL_S atoms are    *)
(* obtained by RETARGETING the template's conclusion -- subst of the PC-      *)
(* offset num-terms and the bytes128/aligned K-address subterms -- and        *)
(* REPLAYING the identical PC-agnostic tactic.  Nothing is hand-typed per     *)
(* group but a parameter row (r, entry/step/exit PC, consumed/next K disp).  *)
(*                                                                           *)
(* Two subtleties baked into the helpers below:                             *)
(*  - `aligned` is polymorphic (num->(N)word->bool); building its hyp by      *)
(*    mk_comb from the bare constant leaves the word width unpinned, so we    *)
(*    vsubst the displacement numeral into a fully-typed template quotation.  *)
(*  - `subst` refuses to rewrite `pc + N` UNDER the enclosing `!pc` binder     *)
(*    (pattern and replacement both mention the bound pc -> would capture),    *)
(*    so retarget_concl strips the foralls (pc becomes free), substs the      *)
(*    body, and re-quantifies.                                               *)
(* ========================================================================= *)

let sm_raw_tmpl_038 = [| SHA256_COMPRESS_HW_GROUP_STEP4_SM;
                         SHA256_COMPRESS_HW_GROUP_STEP4_SM_R1;
                         SHA256_COMPRESS_HW_GROUP_STEP4_SM_R2;
                         SHA256_COMPRESS_HW_GROUP_STEP4_SM_R3 |];;
let sm_pk_tmpl_038  = [| SHA256_COMPRESS_HW_GROUP_STEP4_SM_PACKED;
                         SHA256_COMPRESS_HW_GROUP_STEP4_SM_R1_PACKED;
                         SHA256_COMPRESS_HW_GROUP_STEP4_SM_R2_PACKED;
                         SHA256_COMPRESS_HW_GROUP_STEP4_SM_R3_PACKED |];;
let full_tmpl_038   = [| SHA256_COMPRESS_HW_GROUP4_FULL_S;
                         SHA256_COMPRESS_HW_GROUP4_FULL_S_R1;
                         SHA256_COMPRESS_HW_GROUP4_FULL_S_R2;
                         SHA256_COMPRESS_HW_GROUP4_FULL_S_R3 |];;
let tmpl_pcs_038  = [| (0xf4,0xfc,0x120); (0x120,0x129,0x14d);
                       (0x14d,0x156,0x17a); (0x17a,0x183,0x1a7) |];;
let tmpl_disp_038 = [| (0,32); (32,64); (64,96); (96,128) |];;

(* the 4 seam predicates (ENSURES_SEQUENCE_TAC intermediate assertions), lifted *)
(* from the committed FULL_S_R{0..3} tactics -- no RIP conjunct (the seq tactic *)
(* injects it), only the next-K read + the wk = simd4 word_add (consumed) (held) *)
let seamq_tmpl_038 = [|
 `\s. read RCX s = kptr /\
      read (memory :> bytes128 (word_add kptr (word 32))) s = kq1 /\
      word_subword (read YMM0_SSE s) (0,128) = simd4 word_add (kq:int128) (a3:int128) /\
      word_subword (read YMM1_SSE s) (0,128) = ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
      word_subword (read YMM2_SSE s) (0,128) = CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
      word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
      word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
      word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
      word_subword (read YMM6_SSE s) (0,128) = (a6:int128)` ;
 `\s. read RCX s = kptr /\
      read (memory :> bytes128 (word_add kptr (word 64))) s = kq2 /\
      word_subword (read YMM0_SSE s) (0,128) = simd4 word_add (kq1:int128) (a4:int128) /\
      word_subword (read YMM1_SSE s) (0,128) = ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
      word_subword (read YMM2_SSE s) (0,128) = CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
      word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
      word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
      word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
      word_subword (read YMM6_SSE s) (0,128) = (a6:int128)` ;
 `\s. read RCX s = kptr /\
      read (memory :> bytes128 (word_add kptr (word 96))) s = kq3 /\
      word_subword (read YMM0_SSE s) (0,128) = simd4 word_add (kq2:int128) (a5:int128) /\
      word_subword (read YMM1_SSE s) (0,128) = ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
      word_subword (read YMM2_SSE s) (0,128) = CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
      word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
      word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
      word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
      word_subword (read YMM6_SSE s) (0,128) = (a6:int128)` ;
 `\s. read RCX s = kptr /\
      read (memory :> bytes128 (word_add kptr (word 128))) s = kq4 /\
      word_subword (read YMM0_SSE s) (0,128) = simd4 word_add (kq3:int128) (a6:int128) /\
      word_subword (read YMM1_SSE s) (0,128) = ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
      word_subword (read YMM2_SSE s) (0,128) = CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
      word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
      word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
      word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
      word_subword (read YMM6_SSE s) (0,128) = (a6:int128)` |];;

let pcoff_038 n = mk_comb(mk_comb(`(+):num->num->num`,`pc:num`),mk_small_numeral n);;
let b128_038 d = if d=0 then `bytes128 (kptr:int64)`
             else mk_comb(`bytes128`,
                     mk_comb(mk_comb(`word_add:int64->int64->int64`,`kptr:int64`),
                             mk_comb(`word:num->int64`,mk_small_numeral d)));;
let aligned_038 d = if d=0 then `aligned 16 (kptr:int64)`
             else vsubst [mk_small_numeral d, `nn:num`]
                    `aligned 16 (word_add (kptr:int64) (word nn))`;;
let retarget_concl_038 subl thm =
  let vs, body = strip_forall (concl thm) in list_mk_forall(vs, subst subl body);;
let retarget_sm_038 (ts,tx) (gs,gx) = [ pcoff_038 gs, pcoff_038 ts;  pcoff_038 gx, pcoff_038 tx ];;
let retarget_full_038 (te,tx) (tdc,tdn) (ge,gx) (gdc,gdn) =
  [ pcoff_038 ge, pcoff_038 te;  pcoff_038 gx, pcoff_038 tx;
    b128_038 gdc, b128_038 tdc;  b128_038 gdn, b128_038 tdn;
    aligned_038 gdc, aligned_038 tdc ];;
let retarget_seam_038 tdn gdn = [ b128_038 gdn, b128_038 tdn ];;

let sm_raw_tac_038 =
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s5" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s6" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s7" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s8" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s9" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC SHA256_RNDS2_WK_CONG THEN CONJ_TAC THEN
      CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC) THEN
  TRY REFL_TAC;;
let sm_pk_tac_038 raw_thm =
  let GA = CONV_RULE(TOP_DEPTH_CONV let_CONV)
             (SPECL [`l:int32 list`; `wk:int128`] SHA256_RNDS2_GROUP_ADVANCE) in
  let GA1 = CONJUNCT1 GA and GA2 = CONJUNCT2 GA in
  let ATCF = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`l:int32 list`;
             `word_subword wk (0,32):int32`; `word_subword wk (32,32):int32`;
             `word_subword wk (64,32):int32`; `word_subword wk (96,32):int32`]
            ABEF_TWO_IS_CDGH_FOUR) in
  REPEAT GEN_TAC THEN REWRITE_TAC[CR4] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA2] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM ATCF] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA1] THEN
  MATCH_ACCEPT_TAC raw_thm;;
let full_tac_038 gs seamQ pk_thm =
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC (pcoff_038 gs) seamQ THEN CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
    REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC(REWRITE_RULE[SOME_FLAGS] pk_thm)];;

(* per-group generator: r = rotation; pcs = (entry,step,exit); disp = (consumed,next) *)
let gen_group_038 r (ge,gs,gx) (gdc,gdn) =
  let (te,ts,tx) = tmpl_pcs_038.(r) and (tdc,tdn) = tmpl_disp_038.(r) in
  let sm_raw = prove(retarget_concl_038 (retarget_sm_038 (ts,tx) (gs,gx)) sm_raw_tmpl_038.(r),
                     sm_raw_tac_038) in
  let sm_pk  = prove(retarget_concl_038 (retarget_sm_038 (ts,tx) (gs,gx)) sm_pk_tmpl_038.(r),
                     sm_pk_tac_038 sm_raw) in
  let seamQ  = subst (retarget_seam_038 tdn gdn) seamq_tmpl_038.(r) in
  let full   = prove(retarget_concl_038 (retarget_full_038 (te,tx) (tdc,tdn) (ge,gx) (gdc,gdn))
                          full_tmpl_038.(r),
                     full_tac_038 gs seamQ sm_pk) in
  (sm_raw, sm_pk, full);;

(* ---- the disp32 steady groups: g8..g12.  FULL_S atoms bound to stable names ---- *)
let (_,_,SHA256_COMPRESS_HW_GROUP4_FULL_S_G8)  = gen_group_038 0 (0x1a7,0x1b3,0x1d7) (128,160);;
let (_,_,SHA256_COMPRESS_HW_GROUP4_FULL_S_G9)  = gen_group_038 1 (0x1d7,0x1e3,0x207) (160,192);;
let (_,_,SHA256_COMPRESS_HW_GROUP4_FULL_S_G10) = gen_group_038 2 (0x207,0x213,0x237) (192,224);;
let (_,_,SHA256_COMPRESS_HW_GROUP4_FULL_S_G11) = gen_group_038 3 (0x237,0x243,0x267) (224,256);;
let (_,_,SHA256_COMPRESS_HW_GROUP4_FULL_S_G12) = gen_group_038 0 (0x267,0x273,0x297) (256,288);;

Printf.printf "S038_STEADY_G8  hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_GROUP4_FULL_S_G8))
  (List.length (frees (concl SHA256_COMPRESS_HW_GROUP4_FULL_S_G8)));;
Printf.printf "S038_STEADY_G9  hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_GROUP4_FULL_S_G9))
  (List.length (frees (concl SHA256_COMPRESS_HW_GROUP4_FULL_S_G9)));;
Printf.printf "S038_STEADY_G10 hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_GROUP4_FULL_S_G10))
  (List.length (frees (concl SHA256_COMPRESS_HW_GROUP4_FULL_S_G10)));;
Printf.printf "S038_STEADY_G11 hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_GROUP4_FULL_S_G11))
  (List.length (frees (concl SHA256_COMPRESS_HW_GROUP4_FULL_S_G11)));;
Printf.printf "S038_STEADY_G12 hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_GROUP4_FULL_S_G12))
  (List.length (frees (concl SHA256_COMPRESS_HW_GROUP4_FULL_S_G12)));;
Printf.printf "S038_COMMIT_BLOCK_DONE\n%!";;

(* ------------------------------------------------------------------------- *)
(* Session 038 — g3 (r=3), the negative-K-displacement steady group.         *)
(* g3's K-load is `movdqa xmm0,[rcx-0x20]`, which the stepper normalizes to   *)
(* the address `word_add kptr (word (2^64-32))` (word_neg (word 32)).  So the *)
(* K-read/aligned terms must be STATED in that exact neg-add form, not        *)
(* word_sub -- the read-over-write forwarding only substitutes on a syntactic *)
(* address match.  wnum builds the signed displacement as (2^64+d) for d<0.   *)
(* g3 is otherwise a bog-standard r=3 steady group (held xmm6, msg2 xmm3,     *)
(* paddd xmm4, msg1 xmm5 -- identical register usage to the FULL_S_R3         *)
(* template): entry pc+0xc7, step pc+0xd0, exit pc+0xf4; consumed disp -32,   *)
(* next disp 0 (= g4's [rcx]).                                                *)
(* ------------------------------------------------------------------------- *)

let two64_038 = num_of_string "18446744073709551616";;
let wnum_038 d = if d >= 0 then mk_small_numeral d
             else mk_numeral (two64_038 -/ (num_of_string (string_of_int (-d))));;
let b128sg_038 d = if d=0 then `bytes128 (kptr:int64)`
               else mk_comb(`bytes128`,
                       mk_comb(mk_comb(`word_add:int64->int64->int64`,`kptr:int64`),
                               mk_comb(`word:num->int64`, wnum_038 d)));;
let aligned_sg_038 d = if d=0 then `aligned 16 (kptr:int64)`
               else vsubst [wnum_038 d, `nn:num`]
                      `aligned 16 (word_add (kptr:int64) (word nn))`;;

(* SM parts: PC-only retarget of the r=3 templates (step 0x183->0xd0, exit 0x1a7->0xf4). *)
let g3_sm_sub = [ pcoff_038 0xd0, pcoff_038 0x183;  pcoff_038 0xf4, pcoff_038 0x1a7 ];;
let G3_SM_RAW =
  prove(retarget_concl_038 g3_sm_sub sm_raw_tmpl_038.(3), sm_raw_tac_038);;
let G3_SM_PACKED =
  prove(retarget_concl_038 g3_sm_sub sm_pk_tmpl_038.(3), sm_pk_tac_038 G3_SM_RAW);;

(* FULL: PC (entry 0x17a->0xc7, exit 0x1a7->0xf4) + K addrs (consumed 96->-32, next 128->0). *)
let g3_full_sub = [ pcoff_038 0xc7, pcoff_038 0x17a;  pcoff_038 0xf4, pcoff_038 0x1a7;
                    b128sg_038 (-32), b128_038 96;    b128sg_038 0, b128_038 128;
                    aligned_sg_038 (-32), aligned_038 96 ];;
(* seamQ_R3 with the next-K read retargeted 128->0 (the wk = simd4 word_add kq3 a6 stays). *)
let g3_seamQ = subst [ b128sg_038 0, b128_038 128 ] seamq_tmpl_038.(3);;
let SHA256_COMPRESS_HW_GROUP4_FULL_S_G3 =
  prove(retarget_concl_038 g3_full_sub full_tmpl_038.(3),
        full_tac_038 0xd0 g3_seamQ G3_SM_PACKED);;

Printf.printf "S038_STEADY_G3  hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_GROUP4_FULL_S_G3))
  (List.length (frees (concl SHA256_COMPRESS_HW_GROUP4_FULL_S_G3)));;
Printf.printf "S038_G3_COMMIT_DONE\n%!";;

(* ========================================================================= *)
(* PHASE 4 -- TAIL GROUP g13 (r=1, K+0x120).  Ring is DRAINING: the schedule *)
(* update for this group is only paddd+msg2 (NO sha256msg1 -- xmm3 holds a3),*)
(* and the 2nd sha256rnds2 is reordered BEFORE the final paddd xmm6,xmm7.    *)
(* Crypto is a bog-standard r=1 group advance; ring post keeps xmm3=a3.      *)
(* Entry pc+0x297 (movdqa[rcx+0x120]); K-load leg to pc+0x2a3; exit pc+0x2c2.*)
(* ========================================================================= *)

let SHA256_COMPRESS_HW_GROUP_STEP4_G13_RAW = prove
 (`!pc kbase (kptr:int64) mloc (mval:int128) wk abef cdgh (a3:int128) (a4:int128) (a5:int128) (a6:int128).
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x2a3) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) = (abef:int128) /\
            word_subword (read YMM2_SSE s) (0,128) = (cdgh:int128) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (\s. read RIP s = word (pc + 0x2c2) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM2_SSE s) (0,128) = sha256_rnds2 cdgh abef wk /\
            word_subword (read YMM1_SSE s) (0,128) =
              sha256_rnds2 abef (sha256_rnds2 cdgh abef wk)
                           (word_subword wk (64,64) : int128) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = sha256_msg2 a5 a4 /\
            word_subword (read YMM6_SSE s) (0,128) =
              simd4 word_add a6
                (word_subword
                   (word_ushr
                      ((word_join:int128->int128->256 word) (sha256_msg2 a5 a4) a4)
                      (8 * 4)) (0,128)))
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM5_SSE; YMM6_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s5" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s6" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s7" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC SHA256_RNDS2_WK_CONG THEN CONJ_TAC THEN
      CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC) THEN
  TRY REFL_TAC);;

Printf.printf "S039_G13_RAW hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_GROUP_STEP4_G13_RAW))
  (List.length (frees (concl SHA256_COMPRESS_HW_GROUP_STEP4_G13_RAW)));;

let SHA256_COMPRESS_HW_GROUP_STEP4_G13_PACKED = prove
 (`!pc kbase (kptr:int64) mloc (mval:int128) (l:int32 list) (wk:int128) (a3:int128) (a4:int128) (a5:int128) (a6:int128).
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x2a3) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (\s. read RIP s = word (pc + 0x2c2) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (CR4 l wk)) (EL 3 (CR4 l wk))
                        (EL 6 (CR4 l wk)) (EL 7 (CR4 l wk)) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (CR4 l wk)) (EL 1 (CR4 l wk))
                        (EL 4 (CR4 l wk)) (EL 5 (CR4 l wk)) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = sha256_msg2 a5 a4 /\
            word_subword (read YMM6_SSE s) (0,128) =
              simd4 word_add a6
                (word_subword
                   (word_ushr
                      ((word_join:int128->int128->256 word) (sha256_msg2 a5 a4) a4)
                      (8 * 4)) (0,128)))
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM5_SSE; YMM6_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  let GA = CONV_RULE(TOP_DEPTH_CONV let_CONV)
             (SPECL [`l:int32 list`; `wk:int128`] SHA256_RNDS2_GROUP_ADVANCE) in
  let GA1 = CONJUNCT1 GA and GA2 = CONJUNCT2 GA in
  let ATCF = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`l:int32 list`;
             `word_subword wk (0,32):int32`; `word_subword wk (32,32):int32`;
             `word_subword wk (64,32):int32`; `word_subword wk (96,32):int32`]
            ABEF_TWO_IS_CDGH_FOUR) in
  REPEAT GEN_TAC THEN REWRITE_TAC[CR4] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA2] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM ATCF] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA1] THEN
  MATCH_ACCEPT_TAC SHA256_COMPRESS_HW_GROUP_STEP4_G13_RAW);;

Printf.printf "S039_G13_PACKED hyps=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_GROUP_STEP4_G13_PACKED));;

(* FULL g13 seam atom: K-load[rcx+0x120]+xmm4 (a4)  then packed step.          *)
(* Entry pc+0x297, K-load leg to pc+0x2a3, exit pc+0x2c2.  wk = simd4 add kq a4.*)
(* Threads RCX + the NEXT K quad (mem @ rcx+0x140 = +320) for g14.             *)
let SHA256_COMPRESS_HW_GROUP4_FULL_S_G13 = prove
 (`!pc kbase (kptr:int64) (l:int32 list) (kq:int128) (kq1:int128) a3 a4 a5 a6:int128.
     aligned 16 (word_add (kptr:int64) (word 288))
     ==> ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x297) /\
            read RCX s = kptr /\
            read (memory :> bytes128 (word_add kptr (word 288))) s = kq /\
            read (memory :> bytes128 (word_add kptr (word 320))) s = kq1 /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (\s. read RIP s = word (pc + 0x2c2) /\
            read RCX s = kptr /\
            read (memory :> bytes128 (word_add kptr (word 320))) s = kq1 /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (CR4 l (simd4 word_add kq a4)))
                        (EL 3 (CR4 l (simd4 word_add kq a4)))
                        (EL 6 (CR4 l (simd4 word_add kq a4)))
                        (EL 7 (CR4 l (simd4 word_add kq a4))) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (CR4 l (simd4 word_add kq a4)))
                        (EL 1 (CR4 l (simd4 word_add kq a4)))
                        (EL 4 (CR4 l (simd4 word_add kq a4)))
                        (EL 5 (CR4 l (simd4 word_add kq a4))) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = sha256_msg2 a5 a4 /\
            word_subword (read YMM6_SSE s) (0,128) =
              simd4 word_add a6
                (word_subword
                   (word_ushr
                      ((word_join:int128->int128->256 word) (sha256_msg2 a5 a4) a4)
                      (8 * 4)) (0,128)))
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM5_SSE; YMM6_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x2a3`
   `\s. read RCX s = kptr /\
        read (memory :> bytes128 (word_add kptr (word 320))) s = kq1 /\
        word_subword (read YMM0_SSE s) (0,128) = simd4 word_add kq a4 /\
        word_subword (read YMM1_SSE s) (0,128) =
          ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
        word_subword (read YMM2_SSE s) (0,128) =
          CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
        word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
        word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
        word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
        word_subword (read YMM6_SSE s) (0,128) = (a6:int128)` THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
    REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC(REWRITE_RULE[SOME_FLAGS]
        SHA256_COMPRESS_HW_GROUP_STEP4_G13_PACKED)]);;

Printf.printf "S039_G13_FULL hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_GROUP4_FULL_S_G13))
  (List.length (frees (concl SHA256_COMPRESS_HW_GROUP4_FULL_S_G13)));;
Printf.printf "S039_G13_DONE\n%!";;

(* ========================================================================= *)
(* PHASE 4 -- TAIL GROUP g14 (r=2, K+0x140).  Ring nearly drained: only the  *)
(* LAST sha256msg2 (xmm6,xmm5) remains -- NO palignr, NO schedule paddd, NO   *)
(* msg1.  The movdqa xmm7,xmm8 reloads the saved byteswap mask into scratch   *)
(* xmm7 (dead; xmm7 in MAYCHANGE).  Crypto = standard r=2 CR4 group advance.  *)
(* Entry pc+0x2c2 (movdqa[rcx+0x140]); K-load leg to pc+0x2ce; exit pc+0x2e4.*)
(* ========================================================================= *)

let SHA256_COMPRESS_HW_GROUP_STEP4_G14_RAW = prove
 (`!pc kbase (kptr:int64) mloc (mval:int128) wk abef cdgh (a3:int128) (a4:int128) (a5:int128) (a6:int128).
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x2ce) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) = (abef:int128) /\
            word_subword (read YMM2_SSE s) (0,128) = (cdgh:int128) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (\s. read RIP s = word (pc + 0x2e4) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM2_SSE s) (0,128) = sha256_rnds2 cdgh abef wk /\
            word_subword (read YMM1_SSE s) (0,128) =
              sha256_rnds2 abef (sha256_rnds2 cdgh abef wk)
                           (word_subword wk (64,64) : int128) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = sha256_msg2 a6 a5)
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM6_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s5" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC SHA256_RNDS2_WK_CONG THEN CONJ_TAC THEN
      CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC) THEN
  TRY REFL_TAC);;

Printf.printf "S039_G14_RAW hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_GROUP_STEP4_G14_RAW))
  (List.length (frees (concl SHA256_COMPRESS_HW_GROUP_STEP4_G14_RAW)));;

let SHA256_COMPRESS_HW_GROUP_STEP4_G14_PACKED = prove
 (`!pc kbase (kptr:int64) mloc (mval:int128) (l:int32 list) (wk:int128) (a3:int128) (a4:int128) (a5:int128) (a6:int128).
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x2ce) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (\s. read RIP s = word (pc + 0x2e4) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (CR4 l wk)) (EL 3 (CR4 l wk))
                        (EL 6 (CR4 l wk)) (EL 7 (CR4 l wk)) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (CR4 l wk)) (EL 1 (CR4 l wk))
                        (EL 4 (CR4 l wk)) (EL 5 (CR4 l wk)) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = sha256_msg2 a6 a5)
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM6_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  let GA = CONV_RULE(TOP_DEPTH_CONV let_CONV)
             (SPECL [`l:int32 list`; `wk:int128`] SHA256_RNDS2_GROUP_ADVANCE) in
  let GA1 = CONJUNCT1 GA and GA2 = CONJUNCT2 GA in
  let ATCF = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`l:int32 list`;
             `word_subword wk (0,32):int32`; `word_subword wk (32,32):int32`;
             `word_subword wk (64,32):int32`; `word_subword wk (96,32):int32`]
            ABEF_TWO_IS_CDGH_FOUR) in
  REPEAT GEN_TAC THEN REWRITE_TAC[CR4] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA2] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM ATCF] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA1] THEN
  MATCH_ACCEPT_TAC SHA256_COMPRESS_HW_GROUP_STEP4_G14_RAW);;

Printf.printf "S039_G14_PACKED hyps=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_GROUP_STEP4_G14_PACKED));;

(* FULL g14: K-load[rcx+0x140]+xmm5 (a5) then packed step.                     *)
(* Entry pc+0x2c2, K-load leg to pc+0x2ce, exit pc+0x2e4.  wk = simd4 add kq a5.*)
(* Threads RCX + the NEXT K quad (mem @ rcx+0x160 = +352) for g15.             *)
let SHA256_COMPRESS_HW_GROUP4_FULL_S_G14 = prove
 (`!pc kbase (kptr:int64) (l:int32 list) (kq:int128) (kq1:int128) a3 a4 a5 a6:int128.
     aligned 16 (word_add (kptr:int64) (word 320))
     ==> ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x2c2) /\
            read RCX s = kptr /\
            read (memory :> bytes128 (word_add kptr (word 320))) s = kq /\
            read (memory :> bytes128 (word_add kptr (word 352))) s = kq1 /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (\s. read RIP s = word (pc + 0x2e4) /\
            read RCX s = kptr /\
            read (memory :> bytes128 (word_add kptr (word 352))) s = kq1 /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (CR4 l (simd4 word_add kq a5)))
                        (EL 3 (CR4 l (simd4 word_add kq a5)))
                        (EL 6 (CR4 l (simd4 word_add kq a5)))
                        (EL 7 (CR4 l (simd4 word_add kq a5))) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (CR4 l (simd4 word_add kq a5)))
                        (EL 1 (CR4 l (simd4 word_add kq a5)))
                        (EL 4 (CR4 l (simd4 word_add kq a5)))
                        (EL 5 (CR4 l (simd4 word_add kq a5))) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = sha256_msg2 a6 a5)
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM6_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x2ce`
   `\s. read RCX s = kptr /\
        read (memory :> bytes128 (word_add kptr (word 352))) s = kq1 /\
        word_subword (read YMM0_SSE s) (0,128) = simd4 word_add kq a5 /\
        word_subword (read YMM1_SSE s) (0,128) =
          ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
        word_subword (read YMM2_SSE s) (0,128) =
          CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
        word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
        word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
        word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
        word_subword (read YMM6_SSE s) (0,128) = (a6:int128)` THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
    REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC(REWRITE_RULE[SOME_FLAGS]
        SHA256_COMPRESS_HW_GROUP_STEP4_G14_PACKED)]);;

Printf.printf "S039_G14_FULL hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_GROUP4_FULL_S_G14))
  (List.length (frees (concl SHA256_COMPRESS_HW_GROUP4_FULL_S_G14)));;
Printf.printf "S039_G14_DONE\n%!";;

(* ========================================================================= *)
(* PHASE 4 -- TAIL GROUP g15 (r=3, K+0x160), TERMINAL.  Ring FULLY drained:  *)
(* no schedule ops -- pure 4-round crypto advance.  The loop counter dec rdx *)
(* is interleaved between the two rnds2 (+ 2 nops); Phase 4 is register-only  *)
(* so we absorb the RDX write / flags into MAYCHANGE [RDX] + SOME_FLAGS       *)
(* (faithful over-approx; Phase 6 handles the back-edge ZF).  No next-K quad  *)
(* threaded (last group); the consumed K quad @kptr+352 rides the frame.      *)
(* Entry pc+0x2e4 (movdqa[rcx+0x160]); K-load leg to pc+0x2f0; exit pc+0x302.*)
(* ========================================================================= *)

let SHA256_COMPRESS_HW_GROUP_STEP4_G15_RAW = prove
 (`!pc kbase (kptr:int64) mloc (mval:int128) wk abef cdgh (a3:int128) (a4:int128) (a5:int128) (a6:int128).
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x2f0) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) = (abef:int128) /\
            word_subword (read YMM2_SSE s) (0,128) = (cdgh:int128) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (\s. read RIP s = word (pc + 0x302) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM2_SSE s) (0,128) = sha256_rnds2 cdgh abef wk /\
            word_subword (read YMM1_SSE s) (0,128) =
              sha256_rnds2 abef (sha256_rnds2 cdgh abef wk)
                           (word_subword wk (64,64) : int128) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE] ,, MAYCHANGE [RDX] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s5" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s6" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC SHA256_RNDS2_WK_CONG THEN CONJ_TAC THEN
      CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC) THEN
  TRY REFL_TAC);;

Printf.printf "S039_G15_RAW hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_GROUP_STEP4_G15_RAW))
  (List.length (frees (concl SHA256_COMPRESS_HW_GROUP_STEP4_G15_RAW)));;

let SHA256_COMPRESS_HW_GROUP_STEP4_G15_PACKED = prove
 (`!pc kbase (kptr:int64) mloc (mval:int128) (l:int32 list) (wk:int128) (a3:int128) (a4:int128) (a5:int128) (a6:int128).
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x2f0) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (\s. read RIP s = word (pc + 0x302) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (CR4 l wk)) (EL 3 (CR4 l wk))
                        (EL 6 (CR4 l wk)) (EL 7 (CR4 l wk)) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (CR4 l wk)) (EL 1 (CR4 l wk))
                        (EL 4 (CR4 l wk)) (EL 5 (CR4 l wk)) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE] ,, MAYCHANGE [RDX] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  let GA = CONV_RULE(TOP_DEPTH_CONV let_CONV)
             (SPECL [`l:int32 list`; `wk:int128`] SHA256_RNDS2_GROUP_ADVANCE) in
  let GA1 = CONJUNCT1 GA and GA2 = CONJUNCT2 GA in
  let ATCF = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`l:int32 list`;
             `word_subword wk (0,32):int32`; `word_subword wk (32,32):int32`;
             `word_subword wk (64,32):int32`; `word_subword wk (96,32):int32`]
            ABEF_TWO_IS_CDGH_FOUR) in
  REPEAT GEN_TAC THEN REWRITE_TAC[CR4] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA2] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM ATCF] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA1] THEN
  MATCH_ACCEPT_TAC SHA256_COMPRESS_HW_GROUP_STEP4_G15_RAW);;

Printf.printf "S039_G15_PACKED hyps=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_GROUP_STEP4_G15_PACKED));;

(* FULL g15 (terminal): K-load[rcx+0x160]+xmm6 (a6) then packed step.          *)
(* Entry pc+0x2e4, K-load leg to pc+0x2f0, exit pc+0x302.  wk = simd4 add kq a6.*)
(* No next-K quad -- ring fully drained, this is the last core group.          *)
let SHA256_COMPRESS_HW_GROUP4_FULL_S_G15 = prove
 (`!pc kbase (kptr:int64) (l:int32 list) (kq:int128) a3 a4 a5 a6:int128.
     aligned 16 (word_add (kptr:int64) (word 352))
     ==> ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x2e4) /\
            read RCX s = kptr /\
            read (memory :> bytes128 (word_add kptr (word 352))) s = kq /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (\s. read RIP s = word (pc + 0x302) /\
            read RCX s = kptr /\
            read (memory :> bytes128 (word_add kptr (word 352))) s = kq /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (CR4 l (simd4 word_add kq a6)))
                        (EL 3 (CR4 l (simd4 word_add kq a6)))
                        (EL 6 (CR4 l (simd4 word_add kq a6)))
                        (EL 7 (CR4 l (simd4 word_add kq a6))) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (CR4 l (simd4 word_add kq a6)))
                        (EL 1 (CR4 l (simd4 word_add kq a6)))
                        (EL 4 (CR4 l (simd4 word_add kq a6)))
                        (EL 5 (CR4 l (simd4 word_add kq a6))) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE] ,, MAYCHANGE [RDX] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x2f0`
   `\s. read RCX s = kptr /\
        read (memory :> bytes128 (word_add kptr (word 352))) s = kq /\
        word_subword (read YMM0_SSE s) (0,128) = simd4 word_add kq a6 /\
        word_subword (read YMM1_SSE s) (0,128) =
          ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
        word_subword (read YMM2_SSE s) (0,128) =
          CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
        word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
        word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
        word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
        word_subword (read YMM6_SSE s) (0,128) = (a6:int128)` THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
    REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC(REWRITE_RULE[SOME_FLAGS]
        SHA256_COMPRESS_HW_GROUP_STEP4_G15_PACKED)]);;

Printf.printf "S039_G15_FULL hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_GROUP4_FULL_S_G15))
  (List.length (frees (concl SHA256_COMPRESS_HW_GROUP4_FULL_S_G15)));;
Printf.printf "S039_G15_DONE\n%!";;

(* ========================================================================= *)
(* PHASE 4 -- FEED-FORWARD paddd (register-only ISA layer).  After the 16    *)
(* round groups the two paddd add the SAVED initial ABEF/CDGH (xmm9/xmm10,    *)
(* stashed in g0 by movdqa xmm9,xmm1 / movdqa xmm10,xmm2) back into the       *)
(* compressed xmm1/xmm2 -- the sha256_block feed-forward H_out = compressed + *)
(* H_in, lane-wise (simd4 word_add) in the packed ABEF/CDGH domain.          *)
(* Entry pc+0x302 (= g15 exit), exit pc+0x30c (the jne back-edge).           *)
(* ========================================================================= *)

let SHA256_COMPRESS_HW_FEEDFWD = prove
 (`!pc kbase (abef:int128) (cdgh:int128) (initabef:int128) (initcdgh:int128).
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x302) /\
            word_subword (read YMM1_SSE s) (0,128) = (abef:int128) /\
            word_subword (read YMM2_SSE s) (0,128) = (cdgh:int128) /\
            word_subword (read YMM9_SSE s) (0,128) = (initabef:int128) /\
            word_subword (read YMM10_SSE s) (0,128) = (initcdgh:int128))
       (\s. read RIP s = word (pc + 0x30c) /\
            word_subword (read YMM2_SSE s) (0,128) = simd4 word_add cdgh initcdgh /\
            word_subword (read YMM1_SSE s) (0,128) = simd4 word_add abef initabef)
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM1_SSE; YMM2_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  TRY REFL_TAC);;

Printf.printf "S039_FF hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_FEEDFWD))
  (List.length (frees (concl SHA256_COMPRESS_HW_FEEDFWD)));;

(* ========================================================================= *)
(* PHASE 4 -- CORE_TAIL3: compose the three tail groups g13 g14 g15 into one  *)
(* segment ensures (pc+0x297 -> pc+0x302), validating the tail seams align.   *)
(* Same read-only K-quad WINDOW frame-carry as CORE_4GROUP: g13 drops the     *)
(* two-ahead kq2@+352 (g14 consumes it) so it rides the read-only frame on    *)
(* the composed pre + seamQ1.  Leg 2 (g14) is REFLEXIVE (seamQ1==g14.pre,     *)
(* g14 threads exactly what g15 needs) -> REFL variant; leg 3 (g15) terminal  *)
(* reflexive.  G13/G14/G15 name K-quads generically (kq/kq1) unlike the       *)
(* s037 R-atoms, so rename to kq0/kq1/kq2 by INST of literal vars on SPEC_ALL.*)
(* ========================================================================= *)

let strip_atom th =
  let bod = snd(strip_forall(concl th)) in
  let ens = if is_imp bod then snd(dest_imp bod) else bod in
  let l,c = dest_comb ens in
  let l2,q = dest_comb l in
  let _,p = dest_comb l2 in (p,q,c);;
let vbyname th n = find (fun v -> name_of v = n) (fst(strip_forall(concl th)));;
let conjs_of_lam q = let s,body = dest_abs q in s, conjuncts body;;
let contains s sub =
  let ls=String.length s and lsub=String.length sub in
  let rec go i = i+lsub<=ls && (String.sub s i lsub = sub || go(i+1)) in go 0;;
let is_kread off c =
  is_eq c && contains (string_of_term c) "bytes128"
          && contains (string_of_term c) ("(word " ^ off ^ ")");;
let kread_for s src_svar src_conjs off =
  vsubst[s,src_svar] (find (is_kread off) src_conjs);;

(* Instantiate a FULL tail atom's ring binders (l,a3,a4,a5,a6) to prev post.    *)
let ymm_rhs post nm =
  let _,cs = conjs_of_lam post in
  let hit = find (fun c -> is_eq c && contains (string_of_term(fst(dest_eq c))) nm) cs in
  snd(dest_eq hit);;
let list_of_abef post =
  let ymm1 = ymm_rhs post "YMM1_SSE" in
  rand(rand(rator(rator(rator ymm1))));;
let post_ring q =
  (list_of_abef q, ymm_rhs q "YMM3_SSE", ymm_rhs q "YMM4_SSE",
   ymm_rhs q "YMM5_SSE", ymm_rhs q "YMM6_SSE");;
let inst_ring atomthm l_v a3_v a4_v a5_v a6_v =
  INST [ l_v,  vbyname atomthm "l";  a3_v, vbyname atomthm "a3";
         a4_v, vbyname atomthm "a4"; a5_v, vbyname atomthm "a5";
         a6_v, vbyname atomthm "a6" ] (SPEC_ALL atomthm);;

(* G13/G14/G15 all name their K-quads generically kq (consumed) / kq1 (next),   *)
(* unlike the s037 R-atoms which had distinct kq_i names.  So rename them to     *)
(* distinct kq0/kq1/kq2 by INST of the literal vars on the SPEC_ALL result       *)
(* (vbyname after SPEC_ALL fails -- no binders left).                            *)
let inst_ring_kq atomthm kmap l_v a3_v a4_v a5_v a6_v =
  let base = SPEC_ALL atomthm in
  INST (kmap @
        [ l_v,  vbyname atomthm "l";  a3_v, vbyname atomthm "a3";
          a4_v, vbyname atomthm "a4"; a5_v, vbyname atomthm "a5";
          a6_v, vbyname atomthm "a6" ]) base;;

(* ---- g13 (FULL_S_G13): consumes kq0@+288, threads kq1@+320 ---- *)
let vG13 = SHA256_COMPRESS_HW_GROUP4_FULL_S_G13;;
let g13th = INST [`kq0:int128`, `kq:int128`; `kq1:int128`, `kq1:int128`]
                 (SPEC_ALL vG13);;
let (pg13,qg13,cg13) = strip_atom g13th;;
let (l13,a313,a413,a513,a613) = post_ring qg13;;

(* ---- g14 (FULL_S_G14): consumes kq1@+320, threads kq2@+352 ----             *)
(* rename g14's kq (consumed @+320) -> kq1, kq1 (next @+352) -> kq2.            *)
let g14th = inst_ring_kq SHA256_COMPRESS_HW_GROUP4_FULL_S_G14
              [ `kq1:int128`, `kq:int128`; `kq2:int128`, `kq1:int128` ]
              l13 a313 a413 a513 a613;;
let (pg14,qg14,cg14) = strip_atom g14th;;
let (l14,a314,a414,a514,a614) = post_ring qg14;;

(* ---- g15 (FULL_S_G15, terminal): consumes kq2@+352 ---- *)
let g15th = inst_ring_kq SHA256_COMPRESS_HW_GROUP4_FULL_S_G15
              [ `kq2:int128`, `kq:int128` ]
              l14 a314 a414 a514 a614;;
let (pg15,qg15,cg15) = strip_atom g15th;;

(* -- state vars + pre conjunct lists -- *)
let svar13,pg13c = conjs_of_lam pg13;;
let sg14,pg14c = conjs_of_lam pg14;;
let sg15,pg15c = conjs_of_lam pg15;;

(* -- composed FRAME = union of all three (g15 adds RDX; g13/g14 add YMM3..7) -- *)
let full_frame =
  `MAYCHANGE [RIP] ,,
   MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM5_SSE; YMM6_SSE; YMM7_SSE] ,,
   MAYCHANGE [RDX] ,,
   MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;

(* -- composed PRE = g13.pre + the two-ahead kq2@+352 (from g14 pre) -- *)
let pre_extra = [ kread_for svar13 sg14 pg14c "352" ];;
let pre_lam = mk_abs(svar13, list_mk_conj (pg13c @ pre_extra));;
let post_lam = qg15;;

let ens_head = rator(rator(rator(snd(dest_imp(snd(strip_forall(concl vG13)))))));;
let mk_ensures p q c = mk_comb(mk_comb(mk_comb(ens_head,p),q),c);;
let bvars = [`pc:num`;`kbase:num`;`kptr:int64`;`l:int32 list`;
             `kq0:int128`;`kq1:int128`;`kq2:int128`;
             `a3:int128`;`a4:int128`;`a5:int128`;`a6:int128`];;
let hyps = list_mk_conj
  [`aligned 16 (word_add (kptr:int64) (word 288))`;
   `aligned 16 (word_add (kptr:int64) (word 320))`;
   `aligned 16 (word_add (kptr:int64) (word 352))`];;
let comp_concl = list_mk_forall(bvars, mk_imp(hyps, mk_ensures pre_lam post_lam full_frame));;

(* -- seams (minus bytes_loaded+RIP) -- *)
let seam_core pre =
  let s,cs = conjs_of_lam pre in
  let keep c = not(contains (string_of_term c) "bytes_loaded")
               && not(contains (string_of_term c) "read RIP") in
  (s, filter keep cs);;
(* seamQ1 @0x2c2 (before g14): g14.pre + carried kq2@+352 (already in g14.pre!  *)
(* g14.pre reads kq1@+320 and kq2@+352, so it is exactly reflexive here).       *)
let seamQ1 = let s,cs = seam_core pg14 in mk_abs(s, list_mk_conj cs);;
(* seamQ2 @0x2e4 (before g15): g15.pre exactly (reflexive terminal). *)
let seamQ2 = let s,cs = seam_core pg15 in mk_abs(s, list_mk_conj cs);;

(* ------------------------------ THE PROOF ------------------------------ *)
let SHA256_COMPRESS_HW_CORE_TAIL3 = prove
 (comp_concl,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x2c2` seamQ1 THEN CONJ_TAC THENL
   [(* leg 1: g13 -- composed pre carries kq2 beyond g13 -> but g13.post threads *)
    (* kq1 only, and seamQ1=g14.pre needs kq1@320+kq2@352; kq2 rides the frame.  *)
    MP_TAC(REWRITE_RULE[SOME_FLAGS] g13th) THEN ASM_REWRITE_TAC[] THEN
    ENSURES_SUBLEMMA_TAC execup "s" "s'" THEN ASM_REWRITE_TAC[];
    ENSURES_SEQUENCE_TAC `pc + 0x2e4` seamQ2 THEN CONJ_TAC THENL
     [(* leg 2: g14 -- seamQ1 == g14.pre exactly, and g14 threads kq2@352 which  *)
      (* is exactly what seamQ2 == g15.pre needs -> nothing rides beyond g14 ->   *)
      (* REFLEXIVE seam (P=>P' collapses to T; stock sublemma's dest_binder fails).*)
      MP_TAC(REWRITE_RULE[SOME_FLAGS] g14th) THEN ASM_REWRITE_TAC[] THEN
      ENSURES_SUBLEMMA_REFL_TAC execup "s" "s'" THEN ASM_REWRITE_TAC[];
      (* leg 3: g15 terminal -- seamQ2 == g15.pre, POST == g15.post -> reflexive *)
      MP_TAC(REWRITE_RULE[SOME_FLAGS] g15th) THEN ASM_REWRITE_TAC[] THEN
      ENSURES_SUBLEMMA_REFL_TAC execup "s" "s'" THEN ASM_REWRITE_TAC[]]]);;

Printf.printf "S039_CORE_TAIL3 hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_CORE_TAIL3))
  (List.length (frees (concl SHA256_COMPRESS_HW_CORE_TAIL3)));;
Printf.printf "S039_TAIL3_DONE\n%!";;

(* ========================================================================= *)
(* Phase 5 -- head: ENTRY state load + repack into ABEF/CDGH (register/load).  *)
(*                                                                            *)
(* The prologue (pc+0x07 .. pc+0x38, ending at the jmp into the oop_shaext     *)
(* body) loads the 8-word input state as two 128-bit quads                     *)
(*   q0 = [rdi]      = {state0,state1,state2,state3}  (state0 in the low dword) *)
(*   q1 = [rdi+0x10] = {state4,state5,state6,state7}                            *)
(* loads the byteswap mask into xmm7 and xmm8 (movdqa [rcx+0x180]; movdqa       *)
(* xmm8,xmm7), and repacks q0/q1 into the SHA-NI ABEF/CDGH register views via   *)
(*   pshufd xmm0,xmm1,0x1b   (reverse dwords)                                   *)
(*   pshufd xmm1,xmm1,0xb1   pshufd xmm2,xmm2,0x1b                              *)
(*   palignr xmm1,xmm2,0x8   punpcklqdq xmm2,xmm0.                              *)
(* Net effect (verified by symbolic stepping): xmm1 = ABEF_PACK of {A,B,E,F}    *)
(* (=state {0,1,4,5}), xmm2 = CDGH_PACK of {C,D,G,H} (=state {2,3,6,7}) -- i.e. *)
(* exactly the crypto-register invariant the g0 group entry expects, with the   *)
(* working list l = the 8 input state words.  No pshufb here (the message       *)
(* byteswaps are in g0..g2), so this is clean register+load algebra.  The       *)
(* movdqa mask load needs `aligned 16 (kptr+384)` or the stepper spins          *)
(* (see the MOVDQA alignment note); 384 = 0x180 is a multiple of 16 so the      *)
(* wrapper discharges it.  The residual pack legs differ only by word_join      *)
(* re-association (stepper's palignr/punpcklqdq 2-2 nesting vs the right-nested *)
(* ABEF_PACK/CDGH_PACK bodies); closed by WORD_BLAST on the 4-lane int128.      *)
let SHA256_COMPRESS_HW_ENTRY_REPACK = prove
 (`!pc kbase (kptr:int64) (dptr:int64) (q0:int128) (q1:int128) (mask:int128).
     aligned 16 (word_add (kptr:int64) (word 384))
     ==> ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x07) /\
            read RCX s = kptr /\
            read RDI s = dptr /\
            read (memory :> bytes128 dptr) s = q0 /\
            read (memory :> bytes128 (word_add dptr (word 16))) s = q1 /\
            read (memory :> bytes128 (word_add kptr (word 384))) s = mask)
       (\s. read RIP s = word (pc + 0x38) /\
            read RCX s = kptr /\
            read RDI s = dptr /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (word_subword q0 (0,32)) (word_subword q0 (32,32))
                        (word_subword q1 (0,32)) (word_subword q1 (32,32)) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (word_subword q0 (64,32)) (word_subword q0 (96,32))
                        (word_subword q1 (64,32)) (word_subword q1 (96,32)) /\
            word_subword (read YMM7_SSE s) (0,128) = mask /\
            word_subword (read YMM8_SSE s) (0,128) = mask)
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM7_SSE; YMM8_SSE] ,,
        MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s5" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s6" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s7" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s8" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s9" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s10" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ABEF_PACK; CDGH_PACK] THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REPEAT CONJ_TAC THEN TRY REFL_TAC THEN CONV_TAC WORD_BLAST);;

Printf.printf "S040_ENTRY_REPACK hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_ENTRY_REPACK))
  (List.length (frees (concl SHA256_COMPRESS_HW_ENTRY_REPACK)));;
Printf.printf "S040_ENTRY_DONE\n%!";;

(* ------------------------------------------------------------------------- *)
(* Phase 5 -- head: pre-g0 message load + first byteswap (ppc 0x38 .. 0x50).   *)
(*                                                                            *)
(* Right after the entry jmp, the body loads the four raw little-endian        *)
(* message quads and byteswaps the first one, before the g0 K-load:            *)
(*   movdqu xmm3,[rsi]; movdqu xmm4,[rsi+0x10]; movdqu xmm5,[rsi+0x20];         *)
(*   pshufb xmm3,xmm7;  movdqu xmm6,[rsi+0x30].                                 *)
(* xmm7 holds the concrete byteswap mask.  At the exit (the g0 K-load pc+0x50)  *)
(* xmm3 = usimd4 word_bytereverse m0 (big-endian message quad 0); xmm4/5/6      *)
(* still hold their raw quads m1/m2/m3 (their byteswaps are staggered into      *)
(* g0/g1/g2).                                                                   *)
(*                                                                            *)
(* CLOSER NOTE (the in-context PSHUFB byteswap recipe): X86_STEPS delivers the  *)
(* pshufb FULLY UNFOLDED (there is no residual `usimd16 f8 ix` -- x86_execute    *)
(* inlines usimd16/usimd8/usimd2), so the folded PSHUFB_BYTESWAP lemma does NOT  *)
(* rewrite in place.  Instead close the byteswap conjunct with PSHUFB_BYTESWAP's *)
(* PROOF recipe inline: expand the RHS usimd4 word_bytereverse (usimd4;usimd2 +  *)
(* DIMINDEX + a WORD_BLAST int32 LANE byte-join lemma), evaluate the ground mask *)
(* selector bytes with WORD_REDUCE_CONV, collapse the operand lens and numerals  *)
(* (WORD_SIMPLE_SUBWORD_CONV + NUM_REDUCE_CONV), then reconcile the two concrete *)
(* 16-byte joins with WORD_BLAST.  (Movdqu loads are unguarded -- no alignment   *)
(* precondition needed here, unlike the movdqa mask load in ENTRY_REPACK.)       *)
let SHA256_COMPRESS_HW_HEAD_MSGLOAD0 = prove
 (`!pc kbase (kptr:int64) (mptr:int64)
      (m0:int128) (m1:int128) (m2:int128) (m3:int128).
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x38) /\
            read RCX s = kptr /\
            read RSI s = mptr /\
            word_subword (read YMM7_SSE s) (0,128) =
              (word 16018520953223639909183530438118932995 : int128) /\
            read (memory :> bytes128 mptr) s = m0 /\
            read (memory :> bytes128 (word_add mptr (word 16))) s = m1 /\
            read (memory :> bytes128 (word_add mptr (word 32))) s = m2 /\
            read (memory :> bytes128 (word_add mptr (word 48))) s = m3)
       (\s. read RIP s = word (pc + 0x50) /\
            read RCX s = kptr /\
            read RSI s = mptr /\
            word_subword (read YMM3_SSE s) (0,128) = usimd4 word_bytereverse m0 /\
            word_subword (read YMM4_SSE s) (0,128) = m1 /\
            word_subword (read YMM5_SSE s) (0,128) = m2 /\
            word_subword (read YMM6_SSE s) (0,128) = m3 /\
            word_subword (read YMM7_SSE s) (0,128) =
              (word 16018520953223639909183530438118932995 : int128))
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM3_SSE; YMM4_SSE; YMM5_SSE; YMM6_SSE] ,,
        MAYCHANGE [events])`,
  let LANE = WORD_BLAST
    `word_bytereverse (w:int32) =
       (word_join:byte->24 word->int32) (word_subword w (0,8))
        ((word_join:byte->16 word->24 word) (word_subword w (8,8))
         ((word_join:byte->8 word->16 word) (word_subword w (16,8))
          (word_subword w (24,8))))` in
  REPEAT GEN_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s5" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[usimd4; usimd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  GEN_REWRITE_TAC (DEPTH_CONV) [LANE] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_BLAST);;

Printf.printf "S040_HEAD_MSGLOAD0 hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_HEAD_MSGLOAD0))
  (List.length (frees (concl SHA256_COMPRESS_HW_HEAD_MSGLOAD0)));;
Printf.printf "S040_MSGLOAD0_DONE\n%!";;

(* ===================================================================== *)
(* PHASE 5 -- HEAD GROUP g0 (bespoke: staggered byteswap + feed-fwd saves) *)
(* g0 crypto leg pc+0x59 -> pc+0x76.  Unique to g0:                        *)
(*   - pshufb xmm4,xmm7 : staggered byteswap of message quad m1 -> W1      *)
(*   - movdqa xmm10,xmm2: SAVE initial CDGH for the feed-forward           *)
(*   - movdqa xmm9,xmm1 : SAVE initial ABEF for the feed-forward           *)
(* Crypto = standard 2x sha256rnds2 (CR4 advance).  NO msg1/msg2, NO flags.*)
(* A generic memory read (mloc/mval) rides through so the FULL atom can    *)
(* thread the next-K quad (as in G13_RAW/PACKED).  Mask baked concrete.    *)
(* ===================================================================== *)

let SHA256_COMPRESS_HW_GROUP_STEP4_G0_RAW = prove
 (`!pc kbase (kptr:int64) mloc (mval:int128) wk abef cdgh (a3:int128) (m1r:int128).
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x59) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) = (abef:int128) /\
            word_subword (read YMM2_SSE s) (0,128) = (cdgh:int128) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (m1r:int128) /\
            word_subword (read YMM7_SSE s) (0,128) =
              (word 16018520953223639909183530438118932995 : int128))
       (\s. read RIP s = word (pc + 0x76) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM2_SSE s) (0,128) = sha256_rnds2 cdgh abef wk /\
            word_subword (read YMM1_SSE s) (0,128) =
              sha256_rnds2 abef (sha256_rnds2 cdgh abef wk)
                           (word_subword wk (64,64) : int128) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = usimd4 word_bytereverse m1r /\
            word_subword (read YMM7_SSE s) (0,128) =
              (word 16018520953223639909183530438118932995 : int128) /\
            word_subword (read YMM9_SSE s) (0,128) = (abef:int128) /\
            word_subword (read YMM10_SSE s) (0,128) = (cdgh:int128))
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM4_SSE; YMM9_SSE; YMM10_SSE] ,,
        MAYCHANGE [events])`,
  let LANE = WORD_BLAST
    `word_bytereverse (w:int32) =
       (word_join:byte->24 word->int32) (word_subword w (0,8))
        ((word_join:byte->16 word->24 word) (word_subword w (8,8))
         ((word_join:byte->8 word->16 word) (word_subword w (16,8))
          (word_subword w (24,8))))` in
  REPEAT GEN_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s5" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s6" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s7" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC SHA256_RNDS2_WK_CONG THEN CONJ_TAC THEN
      CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC) THEN
  TRY REFL_TAC THEN
  REWRITE_TAC[usimd4; usimd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  GEN_REWRITE_TAC (DEPTH_CONV) [LANE] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_BLAST);;

Printf.printf "S041_G0_RAW hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_GROUP_STEP4_G0_RAW))
  (List.length (frees (concl SHA256_COMPRESS_HW_GROUP_STEP4_G0_RAW)));;

let SHA256_COMPRESS_HW_GROUP_STEP4_G0_PACKED = prove
 (`!pc kbase (kptr:int64) mloc (mval:int128) (l:int32 list) (wk:int128) (a3:int128) (m1r:int128).
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x59) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (m1r:int128) /\
            word_subword (read YMM7_SSE s) (0,128) =
              (word 16018520953223639909183530438118932995 : int128))
       (\s. read RIP s = word (pc + 0x76) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (CR4 l wk)) (EL 3 (CR4 l wk))
                        (EL 6 (CR4 l wk)) (EL 7 (CR4 l wk)) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (CR4 l wk)) (EL 1 (CR4 l wk))
                        (EL 4 (CR4 l wk)) (EL 5 (CR4 l wk)) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = usimd4 word_bytereverse m1r /\
            word_subword (read YMM7_SSE s) (0,128) =
              (word 16018520953223639909183530438118932995 : int128) /\
            word_subword (read YMM9_SSE s) (0,128) =
              ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
            word_subword (read YMM10_SSE s) (0,128) =
              CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l))
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM4_SSE; YMM9_SSE; YMM10_SSE] ,,
        MAYCHANGE [events])`,
  let GA = CONV_RULE(TOP_DEPTH_CONV let_CONV)
             (SPECL [`l:int32 list`; `wk:int128`] SHA256_RNDS2_GROUP_ADVANCE) in
  let GA1 = CONJUNCT1 GA and GA2 = CONJUNCT2 GA in
  let ATCF = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`l:int32 list`;
             `word_subword wk (0,32):int32`; `word_subword wk (32,32):int32`;
             `word_subword wk (64,32):int32`; `word_subword wk (96,32):int32`]
            ABEF_TWO_IS_CDGH_FOUR) in
  REPEAT GEN_TAC THEN REWRITE_TAC[CR4] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA2] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM ATCF] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA1] THEN
  MATCH_ACCEPT_TAC SHA256_COMPRESS_HW_GROUP_STEP4_G0_RAW);;

Printf.printf "S041_G0_PACKED hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_GROUP_STEP4_G0_PACKED))
  (List.length (frees (concl SHA256_COMPRESS_HW_GROUP_STEP4_G0_PACKED)));;

(* g0 FULL_S: K-load [rcx-0x80] (neg disp -128 = 2^64-128) + paddd xmm0,xmm3.
   wk = simd4 word_add kq0 a3  (a3 = W0, the bswapped m0 from HEAD_MSGLOAD0).
   Entry pc+0x50, K-load leg to pc+0x59, exit pc+0x76.  Threads RCX + the ONE
   next-K quad (kq1@rcx-0x60 = -96, for g1) on the read-only frame, plus the
   saved feed-forward regs YMM9/YMM10.  a3, m1r held. *)
let SHA256_COMPRESS_HW_GROUP4_FULL_S_G0 = prove
 (`!pc kbase (kptr:int64) (l:int32 list) (kq0:int128) (kq1:int128)
      (a3:int128) (m1r:int128).
     aligned 16 (word_add (kptr:int64) (word 18446744073709551488))
     ==> ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x50) /\
            read RCX s = kptr /\
            read (memory :> bytes128 (word_add kptr (word 18446744073709551488))) s = kq0 /\
            read (memory :> bytes128 (word_add kptr (word 18446744073709551520))) s = kq1 /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (m1r:int128) /\
            word_subword (read YMM7_SSE s) (0,128) =
              (word 16018520953223639909183530438118932995 : int128))
       (\s. read RIP s = word (pc + 0x76) /\
            read RCX s = kptr /\
            read (memory :> bytes128 (word_add kptr (word 18446744073709551520))) s = kq1 /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (CR4 l (simd4 word_add kq0 a3)))
                        (EL 3 (CR4 l (simd4 word_add kq0 a3)))
                        (EL 6 (CR4 l (simd4 word_add kq0 a3)))
                        (EL 7 (CR4 l (simd4 word_add kq0 a3))) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (CR4 l (simd4 word_add kq0 a3)))
                        (EL 1 (CR4 l (simd4 word_add kq0 a3)))
                        (EL 4 (CR4 l (simd4 word_add kq0 a3)))
                        (EL 5 (CR4 l (simd4 word_add kq0 a3))) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = usimd4 word_bytereverse m1r /\
            word_subword (read YMM7_SSE s) (0,128) =
              (word 16018520953223639909183530438118932995 : int128) /\
            word_subword (read YMM9_SSE s) (0,128) =
              ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
            word_subword (read YMM10_SSE s) (0,128) =
              CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l))
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM4_SSE; YMM9_SSE; YMM10_SSE] ,,
        MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + 0x59`
   `\s. read RCX s = kptr /\
        read (memory :> bytes128 (word_add kptr (word 18446744073709551520))) s = kq1 /\
        word_subword (read YMM0_SSE s) (0,128) = simd4 word_add kq0 a3 /\
        word_subword (read YMM1_SSE s) (0,128) =
          ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
        word_subword (read YMM2_SSE s) (0,128) =
          CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
        word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
        word_subword (read YMM4_SSE s) (0,128) = (m1r:int128) /\
        word_subword (read YMM7_SSE s) (0,128) =
          (word 16018520953223639909183530438118932995 : int128)` THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
    REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC SHA256_COMPRESS_HW_GROUP_STEP4_G0_PACKED]);;

Printf.printf "S041_G0_FULL hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_GROUP4_FULL_S_G0))
  (List.length (frees (concl SHA256_COMPRESS_HW_GROUP4_FULL_S_G0)));;
Printf.printf "S041_G0_DONE\n%!";;

(* ===================================================================== *)
(* PHASE 5 -- HEAD GROUP g1 (bespoke: staggered byteswap + FIRST msg1).  *)
(* g1 crypto leg pc+0x7b -> pc+0x99.  Instructions:                       *)
(*   pshufb xmm5,xmm7 : staggered byteswap m2 -> W2                        *)
(*   2x sha256rnds2   : CR4 group advance (wk from K[rcx-0x60]+W1)         *)
(*   pshufd xmm0,0xe  : round-2 wk high64                                  *)
(*   lea rsi,[rsi+0x40] : advance the data pointer (RSI write, NO flags)   *)
(*   sha256msg1 xmm3,xmm4 : FIRST schedule ring update, xmm3' = msg1 W0 W1 *)
(* NO msg2 yet (ring still building).  a3=W0(=xmm3), a4=W1(=xmm4).         *)
(* ===================================================================== *)

let SHA256_COMPRESS_HW_GROUP_STEP4_G1_RAW = prove
 (`!pc kbase (kptr:int64) (dptr:int64) mloc (mval:int128)
      wk abef cdgh (a3:int128) (a4:int128) (m2r:int128).
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x7f) /\
            read RCX s = kptr /\
            read RSI s = dptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) = (abef:int128) /\
            word_subword (read YMM2_SSE s) (0,128) = (cdgh:int128) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (m2r:int128) /\
            word_subword (read YMM7_SSE s) (0,128) =
              (word 16018520953223639909183530438118932995 : int128))
       (\s. read RIP s = word (pc + 0x99) /\
            read RCX s = kptr /\
            read RSI s = word_add dptr (word 0x40) /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM2_SSE s) (0,128) = sha256_rnds2 cdgh abef wk /\
            word_subword (read YMM1_SSE s) (0,128) =
              sha256_rnds2 abef (sha256_rnds2 cdgh abef wk)
                           (word_subword wk (64,64) : int128) /\
            word_subword (read YMM3_SSE s) (0,128) = sha256_msg1 a3 a4 /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = usimd4 word_bytereverse m2r /\
            word_subword (read YMM7_SSE s) (0,128) =
              (word 16018520953223639909183530438118932995 : int128))
       (MAYCHANGE [RIP; RSI] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM5_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  let LANE = WORD_BLAST
    `word_bytereverse (w:int32) =
       (word_join:byte->24 word->int32) (word_subword w (0,8))
        ((word_join:byte->16 word->24 word) (word_subword w (8,8))
         ((word_join:byte->8 word->16 word) (word_subword w (16,8))
          (word_subword w (24,8))))` in
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s5" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s6" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC SHA256_RNDS2_WK_CONG THEN CONJ_TAC THEN
      CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC) THEN
  TRY REFL_TAC THEN
  REWRITE_TAC[usimd4; usimd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  GEN_REWRITE_TAC (DEPTH_CONV) [LANE] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_BLAST);;

Printf.printf "S041_G1_RAW hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_GROUP_STEP4_G1_RAW))
  (List.length (frees (concl SHA256_COMPRESS_HW_GROUP_STEP4_G1_RAW)));;
Printf.printf "S041_G1RAW_DONE\n%!";;

(* g1 PACKED: crypto post -> CR4 form; schedule (YMM3=msg1) + byteswap pass thru. *)
let SHA256_COMPRESS_HW_GROUP_STEP4_G1_PACKED = prove
 (`!pc kbase (kptr:int64) (dptr:int64) mloc (mval:int128)
      (l:int32 list) (wk:int128) (a3:int128) (a4:int128) (m2r:int128).
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x7f) /\
            read RCX s = kptr /\
            read RSI s = dptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (m2r:int128) /\
            word_subword (read YMM7_SSE s) (0,128) =
              (word 16018520953223639909183530438118932995 : int128))
       (\s. read RIP s = word (pc + 0x99) /\
            read RCX s = kptr /\
            read RSI s = word_add dptr (word 0x40) /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (CR4 l wk)) (EL 3 (CR4 l wk))
                        (EL 6 (CR4 l wk)) (EL 7 (CR4 l wk)) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (CR4 l wk)) (EL 1 (CR4 l wk))
                        (EL 4 (CR4 l wk)) (EL 5 (CR4 l wk)) /\
            word_subword (read YMM3_SSE s) (0,128) = sha256_msg1 a3 a4 /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = usimd4 word_bytereverse m2r /\
            word_subword (read YMM7_SSE s) (0,128) =
              (word 16018520953223639909183530438118932995 : int128))
       (MAYCHANGE [RIP; RSI] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM5_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  let GA = CONV_RULE(TOP_DEPTH_CONV let_CONV)
             (SPECL [`l:int32 list`; `wk:int128`] SHA256_RNDS2_GROUP_ADVANCE) in
  let GA1 = CONJUNCT1 GA and GA2 = CONJUNCT2 GA in
  let ATCF = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`l:int32 list`;
             `word_subword wk (0,32):int32`; `word_subword wk (32,32):int32`;
             `word_subword wk (64,32):int32`; `word_subword wk (96,32):int32`]
            ABEF_TWO_IS_CDGH_FOUR) in
  REPEAT GEN_TAC THEN REWRITE_TAC[CR4] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA2] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM ATCF] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA1] THEN
  MATCH_ACCEPT_TAC SHA256_COMPRESS_HW_GROUP_STEP4_G1_RAW);;

Printf.printf "S041_G1_PACKED hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_GROUP_STEP4_G1_PACKED))
  (List.length (frees (concl SHA256_COMPRESS_HW_GROUP_STEP4_G1_PACKED)));;

(* g1 FULL_S: K-load [rcx-0x60] (disp -96) + paddd xmm0,xmm4 -> wk=simd4 add kq1 a4.
   Entry pc+0x76, K-load leg to pc+0x7f, exit pc+0x99.  Threads RCX + RSI + the
   next-K quad (kq2@rcx-0x40 = -64, for g2). *)
let SHA256_COMPRESS_HW_GROUP4_FULL_S_G1 = prove
 (`!pc kbase (kptr:int64) (dptr:int64) (l:int32 list)
      (kq1:int128) (kq2:int128) (a3:int128) (a4:int128) (m2r:int128).
     aligned 16 (word_add (kptr:int64) (word 18446744073709551520))
     ==> ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x76) /\
            read RCX s = kptr /\
            read RSI s = dptr /\
            read (memory :> bytes128 (word_add kptr (word 18446744073709551520))) s = kq1 /\
            read (memory :> bytes128 (word_add kptr (word 18446744073709551552))) s = kq2 /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (m2r:int128) /\
            word_subword (read YMM7_SSE s) (0,128) =
              (word 16018520953223639909183530438118932995 : int128))
       (\s. read RIP s = word (pc + 0x99) /\
            read RCX s = kptr /\
            read RSI s = word_add dptr (word 0x40) /\
            read (memory :> bytes128 (word_add kptr (word 18446744073709551552))) s = kq2 /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (CR4 l (simd4 word_add kq1 a4)))
                        (EL 3 (CR4 l (simd4 word_add kq1 a4)))
                        (EL 6 (CR4 l (simd4 word_add kq1 a4)))
                        (EL 7 (CR4 l (simd4 word_add kq1 a4))) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (CR4 l (simd4 word_add kq1 a4)))
                        (EL 1 (CR4 l (simd4 word_add kq1 a4)))
                        (EL 4 (CR4 l (simd4 word_add kq1 a4)))
                        (EL 5 (CR4 l (simd4 word_add kq1 a4))) /\
            word_subword (read YMM3_SSE s) (0,128) = sha256_msg1 a3 a4 /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = usimd4 word_bytereverse m2r /\
            word_subword (read YMM7_SSE s) (0,128) =
              (word 16018520953223639909183530438118932995 : int128))
       (MAYCHANGE [RIP; RSI] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM5_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x7f`
   `\s. read RCX s = kptr /\
        read RSI s = dptr /\
        read (memory :> bytes128 (word_add kptr (word 18446744073709551552))) s = kq2 /\
        word_subword (read YMM0_SSE s) (0,128) = simd4 word_add kq1 a4 /\
        word_subword (read YMM1_SSE s) (0,128) =
          ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
        word_subword (read YMM2_SSE s) (0,128) =
          CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
        word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
        word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
        word_subword (read YMM5_SSE s) (0,128) = (m2r:int128) /\
        word_subword (read YMM7_SSE s) (0,128) =
          (word 16018520953223639909183530438118932995 : int128)` THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
    REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC(REWRITE_RULE[SOME_FLAGS]
        SHA256_COMPRESS_HW_GROUP_STEP4_G1_PACKED)]);;

Printf.printf "S041_G1_FULL hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_GROUP4_FULL_S_G1))
  (List.length (frees (concl SHA256_COMPRESS_HW_GROUP4_FULL_S_G1)));;
Printf.printf "S041_G1_DONE\n%!";;


(* ===================================================================== *)
(* PHASE 5 -- HEAD GROUP g2 (bespoke: full schedule step, NO msg2 yet).  *)
(* g2's byteswap of xmm6 is CONSUMED by its own schedule (palignr uses    *)
(* the byteswapped xmm6), so we fold the pshufb into the FULL K-load leg  *)
(* and let RAW treat xmm6 = a6 (the byteswapped W3) as an OPAQUE input --  *)
(* the RAW leg then closes with the plain steady-SM tail (no byteswap     *)
(* recipe, no risky WORD_BLAST on a symbolic int128).                     *)
(* RAW leg pc+0xa7 -> pc+0xc7 (8 steps):                                   *)
(*   sha256rnds2 xmm2 ; pshufd xmm0 ; movdqa xmm7,xmm6 ;                    *)
(*   palignr xmm7,xmm5,0x4 ; nop ; paddd xmm3,xmm7 ;                        *)
(*   sha256msg1 xmm4,xmm5 ; sha256rnds2 xmm1.                               *)
(* xmm3' = a3 + palignr(a6,a5,4) ; xmm4' = msg1 a4 a5 ; xmm5/xmm6 held.     *)
(* ===================================================================== *)

let SHA256_COMPRESS_HW_GROUP_STEP4_G2_RAW = prove
 (`!pc kbase (kptr:int64) mloc (mval:int128)
      wk abef cdgh (a3:int128) (a4:int128) (a5:int128) (a6:int128).
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0xa7) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) = (abef:int128) /\
            word_subword (read YMM2_SSE s) (0,128) = (cdgh:int128) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (\s. read RIP s = word (pc + 0xc7) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM2_SSE s) (0,128) = sha256_rnds2 cdgh abef wk /\
            word_subword (read YMM1_SSE s) (0,128) =
              sha256_rnds2 abef (sha256_rnds2 cdgh abef wk)
                           (word_subword wk (64,64) : int128) /\
            word_subword (read YMM3_SSE s) (0,128) =
              simd4 word_add a3
                (word_subword
                   (word_ushr
                      ((word_join:int128->int128->256 word) a6 a5)
                      (8 * 4)) (0,128)) /\
            word_subword (read YMM4_SSE s) (0,128) = sha256_msg1 a4 a5 /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM6_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s5" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s6" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s7" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s8" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC SHA256_RNDS2_WK_CONG THEN CONJ_TAC THEN
      CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC) THEN
  TRY REFL_TAC);;

Printf.printf "S041_G2_RAW hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_GROUP_STEP4_G2_RAW))
  (List.length (frees (concl SHA256_COMPRESS_HW_GROUP_STEP4_G2_RAW)));;
Printf.printf "S041_G2RAW_DONE\n%!";;

(* g2 PACKED: crypto post -> CR4 form; schedule (YMM3 palignr-add, YMM4 msg1) held. *)
let SHA256_COMPRESS_HW_GROUP_STEP4_G2_PACKED = prove
 (`!pc kbase (kptr:int64) mloc (mval:int128)
      (l:int32 list) (wk:int128) (a3:int128) (a4:int128) (a5:int128) (a6:int128).
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0xa7) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (\s. read RIP s = word (pc + 0xc7) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (CR4 l wk)) (EL 3 (CR4 l wk))
                        (EL 6 (CR4 l wk)) (EL 7 (CR4 l wk)) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (CR4 l wk)) (EL 1 (CR4 l wk))
                        (EL 4 (CR4 l wk)) (EL 5 (CR4 l wk)) /\
            word_subword (read YMM3_SSE s) (0,128) =
              simd4 word_add a3
                (word_subword
                   (word_ushr
                      ((word_join:int128->int128->256 word) a6 a5)
                      (8 * 4)) (0,128)) /\
            word_subword (read YMM4_SSE s) (0,128) = sha256_msg1 a4 a5 /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM6_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  let GA = CONV_RULE(TOP_DEPTH_CONV let_CONV)
             (SPECL [`l:int32 list`; `wk:int128`] SHA256_RNDS2_GROUP_ADVANCE) in
  let GA1 = CONJUNCT1 GA and GA2 = CONJUNCT2 GA in
  let ATCF = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`l:int32 list`;
             `word_subword wk (0,32):int32`; `word_subword wk (32,32):int32`;
             `word_subword wk (64,32):int32`; `word_subword wk (96,32):int32`]
            ABEF_TWO_IS_CDGH_FOUR) in
  REPEAT GEN_TAC THEN REWRITE_TAC[CR4] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA2] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM ATCF] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA1] THEN
  MATCH_ACCEPT_TAC SHA256_COMPRESS_HW_GROUP_STEP4_G2_RAW);;

Printf.printf "S041_G2_PACKED hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_GROUP_STEP4_G2_PACKED))
  (List.length (frees (concl SHA256_COMPRESS_HW_GROUP_STEP4_G2_PACKED)));;

(* g2 FULL_S: K-load leg = movdqa[rcx-0x40] + paddd xmm0,xmm5 + pshufb xmm6,xmm7
   (3 steps: pc+0x99 -> pc+0xa7).  wk = simd4 word_add kq2 a5; the byteswap turns
   the raw m3r into a6 = usimd4 word_bytereverse m3r (fed to the schedule palignr).
   Threads RCX + the next-K quad (kq3@rcx-0x20 = -32, for g3). *)
let SHA256_COMPRESS_HW_GROUP4_FULL_S_G2 = prove
 (`!pc kbase (kptr:int64) (l:int32 list)
      (kq2:int128) (kq3:int128) (a3:int128) (a4:int128) (a5:int128) (m3r:int128).
     aligned 16 (word_add (kptr:int64) (word 18446744073709551552))
     ==> ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x99) /\
            read RCX s = kptr /\
            read (memory :> bytes128 (word_add kptr (word 18446744073709551552))) s = kq2 /\
            read (memory :> bytes128 (word_add kptr (word 18446744073709551584))) s = kq3 /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (m3r:int128) /\
            word_subword (read YMM7_SSE s) (0,128) =
              (word 16018520953223639909183530438118932995 : int128))
       (\s. read RIP s = word (pc + 0xc7) /\
            read RCX s = kptr /\
            read (memory :> bytes128 (word_add kptr (word 18446744073709551584))) s = kq3 /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (CR4 l (simd4 word_add kq2 a5)))
                        (EL 3 (CR4 l (simd4 word_add kq2 a5)))
                        (EL 6 (CR4 l (simd4 word_add kq2 a5)))
                        (EL 7 (CR4 l (simd4 word_add kq2 a5))) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (CR4 l (simd4 word_add kq2 a5)))
                        (EL 1 (CR4 l (simd4 word_add kq2 a5)))
                        (EL 4 (CR4 l (simd4 word_add kq2 a5)))
                        (EL 5 (CR4 l (simd4 word_add kq2 a5))) /\
            word_subword (read YMM3_SSE s) (0,128) =
              simd4 word_add a3
                (word_subword
                   (word_ushr
                      ((word_join:int128->int128->256 word)
                         (usimd4 word_bytereverse m3r) a5)
                      (8 * 4)) (0,128)) /\
            word_subword (read YMM4_SSE s) (0,128) = sha256_msg1 a4 a5 /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) =
              (usimd4 word_bytereverse m3r : int128))
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM6_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  let LANE = WORD_BLAST
    `word_bytereverse (w:int32) =
       (word_join:byte->24 word->int32) (word_subword w (0,8))
        ((word_join:byte->16 word->24 word) (word_subword w (8,8))
         ((word_join:byte->8 word->16 word) (word_subword w (16,8))
          (word_subword w (24,8))))` in
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0xa7`
   `\s. read RCX s = kptr /\
        read (memory :> bytes128 (word_add kptr (word 18446744073709551584))) s = kq3 /\
        word_subword (read YMM0_SSE s) (0,128) = simd4 word_add kq2 a5 /\
        word_subword (read YMM1_SSE s) (0,128) =
          ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
        word_subword (read YMM2_SSE s) (0,128) =
          CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
        word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
        word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
        word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
        word_subword (read YMM6_SSE s) (0,128) =
          (usimd4 word_bytereverse m3r : int128)` THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s3" THEN
    ENSURES_FINAL_STATE_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
    REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY REFL_TAC THEN
    TRY(REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
        CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC) THEN
    TRY(REWRITE_TAC[usimd4; usimd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
        CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
        GEN_REWRITE_TAC (DEPTH_CONV) [LANE] THEN
        CONV_TAC WORD_REDUCE_CONV THEN
        CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        CONV_TAC WORD_BLAST);
    MATCH_ACCEPT_TAC(REWRITE_RULE[SOME_FLAGS]
        SHA256_COMPRESS_HW_GROUP_STEP4_G2_PACKED)]);;

Printf.printf "S041_G2_FULL hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_GROUP4_FULL_S_G2))
  (List.length (frees (concl SHA256_COMPRESS_HW_GROUP4_FULL_S_G2)));;
Printf.printf "S041_G2_DONE\n%!";;

(* ========================================================================= *)
(* Session 042 -- CORE_HEAD_CRYPTO: g0 g1 g2 g3 composed (pc+0x50 -> pc+0xf4). *)
(* The head crypto core with abstract state (l) + abstract raw message quads   *)
(* (a3=W0, m1r,m2r,m3r).  Register roles differ per head group (heterogeneous  *)
(* frames + staggered byteswaps + growing schedule ring + feed-fwd saves), so  *)
(* the groups are chained BESPOKE (not the uniform inst_ring composer): each    *)
(* next group's binders are SPECL'd to the previous group's post occupants,    *)
(* read programmatically.  Read-only carries that ride pre->post through groups *)
(* that don't touch them (validated by the s042 g0 g1 de-risk):                 *)
(*   - RSI=dptr rides through g0; RSI=dptr+0x40 (g1) rides through g2,g3.        *)
(*   - YMM5=m2r rides through g0 (consumed g1); YMM6=m3r rides g0,g1 (cons. g2). *)
(*   - YMM9/YMM10 (init ABEF/CDGH, saved by g0) ride read-only through g1,g2,g3. *)
(*   - K-window quads kq2/kq3/kq4 ride read-only forward to their consumer.      *)
(* Only the CONSUMED K quad per group needs an aligned hyp (one movdqa/group).  *)
(* ========================================================================= *)


(* -- self-contained helpers -- *)
let hc_strip_atom th =
  let bod = snd(strip_forall(concl th)) in
  let ens = if is_imp bod then snd(dest_imp bod) else bod in
  let l,c = dest_comb ens in let l2,q = dest_comb l in let _,p = dest_comb l2 in (p,q,c);;
let hc_conjs_of_lam q = let s,body = dest_abs q in s, conjuncts body;;
let hc_contains s sub =
  let ls=String.length s and lsub=String.length sub in
  let rec go i = i+lsub<=ls && (String.sub s i lsub = sub || go(i+1)) in go 0;;
let hc_find sub cs = find (fun c -> hc_contains (string_of_term c) sub) cs;;
let hc_ymm post nm =
  let _,cs = hc_conjs_of_lam post in
  snd(dest_eq(find (fun c -> is_eq c
        && hc_contains (string_of_term(fst(dest_eq c))) nm) cs));;
let hc_list_of_abef post =
  let y = hc_ymm post "YMM1_SSE" in rand(rand(rator(rator(rator y))));;

let vG0 = SHA256_COMPRESS_HW_GROUP4_FULL_S_G0;;
let vG1 = SHA256_COMPRESS_HW_GROUP4_FULL_S_G1;;
let vG2 = SHA256_COMPRESS_HW_GROUP4_FULL_S_G2;;
let vG3 = SHA256_COMPRESS_HW_GROUP4_FULL_S_G3;;

(* ---- g0: keep binders free (canonical), read its post ---- *)
let g0th = SPEC_ALL vG0;;
let (pg0,qg0,cg0) = hc_strip_atom g0th;;
let svar, pg0c = hc_conjs_of_lam pg0;;               (* canonical state var *)
let canon src cs = let s,_ = src in map (vsubst[svar,s]) cs;;
let _,qg0c0 = hc_conjs_of_lam qg0;; let qg0_svar,_ = hc_conjs_of_lam qg0;;
let qg0c = map (vsubst[svar,qg0_svar]) qg0c0;;
let l1     = hc_list_of_abef qg0;;                   (* CR4 l (simd4 add kq0 a3) *)
let w1     = hc_ymm qg0 "YMM4_SSE";;                 (* usimd4 word_bytereverse m1r *)
let ymm9v  = vsubst[svar,qg0_svar] (hc_find "YMM9_SSE"  qg0c0);;
let ymm10v = vsubst[svar,qg0_svar] (hc_find "YMM10_SSE" qg0c0);;

(* ---- g1: SPECL to g0's post occupants ---- *)
let g1th = SPECL [`pc:num`;`kbase:num`;`kptr:int64`;`dptr:int64`;
                  l1; `kq1:int128`;`kq2:int128`; `a3:int128`; w1; `m2r:int128`] vG1;;
let (pg1,qg1,cg1) = hc_strip_atom g1th;;
let sg1,pg1c0 = hc_conjs_of_lam pg1;; let pg1c = canon (sg1,()) pg1c0;;
let sq1,qg1c0 = hc_conjs_of_lam qg1;; let qg1c = map (vsubst[svar,sq1]) qg1c0;;
let l2     = hc_list_of_abef qg1;;
let g1_y3  = hc_ymm qg1 "YMM3_SSE";;                 (* sha256_msg1 a3 w1 *)
let w2     = hc_ymm qg1 "YMM5_SSE";;                 (* usimd4 word_bytereverse m2r *)
let rsi_post = vsubst[svar,sq1] (hc_find "read RSI" qg1c0);;   (* RSI = dptr+0x40 *)

(* ---- g2: SPECL to g1's post occupants ---- *)
let g2th = SPECL [`pc:num`;`kbase:num`;`kptr:int64`;
                  l2; `kq2:int128`;`kq3:int128`; g1_y3; w1; w2; `m3r:int128`] vG2;;
let (pg2,qg2,cg2) = hc_strip_atom g2th;;
let sg2,pg2c0 = hc_conjs_of_lam pg2;; let pg2c = canon (sg2,()) pg2c0;;
let sq2,qg2c0 = hc_conjs_of_lam qg2;; let qg2c = map (vsubst[svar,sq2]) qg2c0;;
let l3     = hc_list_of_abef qg2;;
let g2_y3  = hc_ymm qg2 "YMM3_SSE";;
let g2_y4  = hc_ymm qg2 "YMM4_SSE";;                 (* sha256_msg1 w1 w2 *)
let g2_y5  = hc_ymm qg2 "YMM5_SSE";;                 (* w2 (held) *)
let g2_y6  = hc_ymm qg2 "YMM6_SSE";;                 (* usimd4 word_bytereverse m3r (=w3) *)

(* ---- g3: SPECL to g2's post occupants ---- *)
let g3th = SPECL [`pc:num`;`kbase:num`;`kptr:int64`;
                  l3; `kq3:int128`;`kq4:int128`; g2_y3; g2_y4; g2_y5; g2_y6] vG3;;
let (pg3,qg3,cg3) = hc_strip_atom g3th;;
let sg3,pg3c0 = hc_conjs_of_lam pg3;; let pg3c = canon (sg3,()) pg3c0;;
let sq3,qg3c0 = hc_conjs_of_lam qg3;; let qg3c = map (vsubst[svar,sq3]) qg3c0;;

(* ---- carried read-only conjuncts (canonical state var) ---- *)
let rsi_pre  = hc_find "read RSI"  pg1c;;            (* RSI = dptr *)
let ymm5_m2r = hc_find "YMM5_SSE"  pg1c;;            (* YMM5 = m2r *)
let ymm6_m3r = hc_find "YMM6_SSE"  pg2c;;            (* YMM6 = m3r *)
let kq2_read = hc_find "(word 18446744073709551552)" pg1c;;   (* kq2 @ -64  *)
let kq3_read = hc_find "(word 18446744073709551584)" pg2c;;   (* kq3 @ -32  *)
let kq4_read = hc_find "bytes128 kptr)" pg3c;;                 (* kq4 @ 0    *)

(* ---- composed PRE = g0.pre + {RSI=dptr, YMM5=m2r, YMM6=m3r, kq2,kq3,kq4} ---- *)
let pre_lam = mk_abs(svar,
  list_mk_conj (pg0c @ [rsi_pre; ymm5_m2r; ymm6_m3r; kq2_read; kq3_read; kq4_read]));;

(* ---- composed POST = g3.post + {RSI=dptr+0x40, YMM9, YMM10} ---- *)
let post_lam = mk_abs(svar, list_mk_conj (qg3c @ [rsi_post; ymm9v; ymm10v]));;

(* ---- composed FRAME = union of all four ---- *)
let comp_frame =
 `MAYCHANGE [RIP; RSI] ,,
  MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM5_SSE;
             YMM6_SSE; YMM7_SSE; YMM9_SSE; YMM10_SSE] ,,
  MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;

(* ---- hyps: aligned on each consumed K quad ---- *)
let comp_hyps = list_mk_conj
 [`aligned 16 (word_add (kptr:int64) (word 18446744073709551488))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551520))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551552))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551584))`];;

let ens_head = rator(rator(rator(snd(dest_imp(snd(strip_forall(concl vG0)))))));;
let mk_ensures p q c = mk_comb(mk_comb(mk_comb(ens_head,p),q),c);;
let bvars = [`pc:num`;`kbase:num`;`kptr:int64`;`dptr:int64`;`l:int32 list`;
             `kq0:int128`;`kq1:int128`;`kq2:int128`;`kq3:int128`;`kq4:int128`;
             `a3:int128`;`m1r:int128`;`m2r:int128`;`m3r:int128`];;
let comp_concl =
  list_mk_forall(bvars, mk_imp(comp_hyps, mk_ensures pre_lam post_lam comp_frame));;

(* ---- seams (minus bytes_loaded + read RIP), plus carried facts ---- *)
let keep c = not(hc_contains (string_of_term c) "bytes_loaded")
             && not(hc_contains (string_of_term c) "read RIP");;
let core cs = filter keep cs;;
(* seam@0x76 (before g1) = g1.pre-core + {YMM6=m3r, YMM9, YMM10, kq3, kq4} *)
let seamQ1 = mk_abs(svar,
  list_mk_conj (core pg1c @ [ymm6_m3r; ymm9v; ymm10v; kq3_read; kq4_read]));;
(* seam@0x99 (before g2) = g2.pre-core + {RSI=dptr+0x40, YMM9, YMM10, kq4} *)
let seamQ2 = mk_abs(svar,
  list_mk_conj (core pg2c @ [rsi_post; ymm9v; ymm10v; kq4_read]));;
(* seam@0xc7 (before g3) = g3.pre-core + {RSI=dptr+0x40, YMM9, YMM10} *)
let seamQ3 = mk_abs(svar,
  list_mk_conj (core pg3c @ [rsi_post; ymm9v; ymm10v]));;

Printf.printf "S042_HEADCRYPTO concl built\n%!";;

let SHA256_COMPRESS_HW_CORE_HEAD_CRYPTO = prove
 (comp_concl,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x76` seamQ1 THEN CONJ_TAC THENL
   [MP_TAC(REWRITE_RULE[SOME_FLAGS] g0th) THEN ASM_REWRITE_TAC[] THEN
    ENSURES_SUBLEMMA_TAC execup "s" "s'" THEN ASM_REWRITE_TAC[];
    ENSURES_SEQUENCE_TAC `pc + 0x99` seamQ2 THEN CONJ_TAC THENL
     [MP_TAC(REWRITE_RULE[SOME_FLAGS] g1th) THEN ASM_REWRITE_TAC[] THEN
      ENSURES_SUBLEMMA_TAC execup "s" "s'" THEN ASM_REWRITE_TAC[];
      ENSURES_SEQUENCE_TAC `pc + 0xc7` seamQ3 THEN CONJ_TAC THENL
       [MP_TAC(REWRITE_RULE[SOME_FLAGS] g2th) THEN ASM_REWRITE_TAC[] THEN
        ENSURES_SUBLEMMA_TAC execup "s" "s'" THEN ASM_REWRITE_TAC[];
        MP_TAC(REWRITE_RULE[SOME_FLAGS] g3th) THEN ASM_REWRITE_TAC[] THEN
        ENSURES_SUBLEMMA_TAC execup "s" "s'" THEN ASM_REWRITE_TAC[]]]]);;

Printf.printf "S042_CORE_HEAD_CRYPTO hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_CORE_HEAD_CRYPTO))
  (List.length (frees (concl SHA256_COMPRESS_HW_CORE_HEAD_CRYPTO)));;
Printf.printf "S042_HEADCRYPTO_DONE\n%!";;

(* ========================================================================= *)
(* Session 042 -- CORE_HEAD: ENTRY_REPACK ; HEAD_MSGLOAD0 ; CORE_HEAD_CRYPTO   *)
(* composed into the full head segment (pc+0x07 -> pc+0xf4).                   *)
(*                                                                            *)
(* Two distinct pointers: RDI = sptr (state array, read at ENTRY -> q0,q1),   *)
(* RSI = mptr (message block, read at MSGLOAD -> m0..m3, advanced by g1's lea).*)
(* ENTRY's abstract byteswap-mask binder is INSTANTIATED to the concrete       *)
(* rodata literal so it matches HEAD_MSGLOAD0's YMM7 requirement.  CRYPTO's     *)
(* working list l is instantiated to the 8 state words (word_subword q0/q1)    *)
(* and EL_CONV-reduced so its ABEF/CDGH_PACK(EL k l) pre matches ENTRY's post.  *)
(*                                                                            *)
(* Read-only riders (validated in the g0;g1 de-risk + CORE_HEAD_CRYPTO):       *)
(*   - RSI=mptr + the 4 message memory reads ride through ENTRY (RSI, memory   *)
(*     not in ENTRY's frame) to feed MSGLOAD.                                  *)
(*   - the 5 K memory reads ride through ENTRY+MSGLOAD to feed CRYPTO.          *)
(*   - YMM1/YMM2 (ENTRY's ABEF/CDGH pack) ride read-only through MSGLOAD.       *)
(*   - RDI=sptr rides read-only through ALL of MSGLOAD+CRYPTO (hook for the     *)
(*     Phase-5 exit state store) into the composed post.                       *)
(* All three legs are non-reflexive (each seam strictly extends the sub-       *)
(* lemma's pre by carried riders) -> stock ENSURES_SUBLEMMA_TAC.               *)
(* ========================================================================= *)


let ch_strip_atom th =
  let bod = snd(strip_forall(concl th)) in
  let ens = if is_imp bod then snd(dest_imp bod) else bod in
  let l,c = dest_comb ens in let l2,q = dest_comb l in let _,p = dest_comb l2 in (p,q,c);;
let ch_conjs q = let s,body = dest_abs q in s, conjuncts body;;
let ch_contains s sub =
  let ls=String.length s and lsub=String.length sub in
  let rec go i = i+lsub<=ls && (String.sub s i lsub = sub || go(i+1)) in go 0;;
let ch_find sub cs = find (fun c -> ch_contains (string_of_term c) sub) cs;;

(* concrete instantiation atoms *)
let masklit = `word 16018520953223639909183530438118932995 : int128`;;
let brm0 = `usimd4 word_bytereverse (m0:int128) : int128`;;
let stlist =
  `[(word_subword (q0:int128) (0,32):int32); (word_subword (q0:int128) (32,32):int32);
    (word_subword (q0:int128) (64,32):int32); (word_subword (q0:int128) (96,32):int32);
    (word_subword (q1:int128) (0,32):int32); (word_subword (q1:int128) (32,32):int32);
    (word_subword (q1:int128) (64,32):int32); (word_subword (q1:int128) (96,32):int32)]`;;

(* -- instantiated sub-lemmas -- *)
let entry_i = SPECL [`pc:num`;`kbase:num`;`kptr:int64`;`sptr:int64`;
                     `q0:int128`;`q1:int128`; masklit] SHA256_COMPRESS_HW_ENTRY_REPACK;;
let msg_i   = SPECL [`pc:num`;`kbase:num`;`kptr:int64`;`mptr:int64`;
                     `m0:int128`;`m1:int128`;`m2:int128`;`m3:int128`]
                SHA256_COMPRESS_HW_HEAD_MSGLOAD0;;
let crypto_i0 = SPECL [`pc:num`;`kbase:num`;`kptr:int64`;`mptr:int64`; stlist;
                       `kq0:int128`;`kq1:int128`;`kq2:int128`;`kq3:int128`;`kq4:int128`;
                       brm0; `m1:int128`;`m2:int128`;`m3:int128`]
                  SHA256_COMPRESS_HW_CORE_HEAD_CRYPTO;;
let crypto_i = CONV_RULE(DEPTH_CONV EL_CONV) crypto_i0;;

(* -- canonical state var = ENTRY.pre's -- *)
let (peE,poE,frE) = ch_strip_atom entry_i;;
let sv, peEc = ch_conjs peE;;
let rebase src cs = let s,_ = ch_conjs src in map (vsubst[sv,s]) cs;;
let poEc = rebase poE (snd(ch_conjs poE));;
let (peM,poM,frM) = ch_strip_atom msg_i;;
let peMc = rebase peM (snd(ch_conjs peM));;
let poMc = rebase poM (snd(ch_conjs poM));;
let (peC,poC,frC) = ch_strip_atom crypto_i;;
let peCc = rebase peC (snd(ch_conjs peC));;
let poCc = rebase poC (snd(ch_conjs poC));;

(* -- key carried facts (canonical sv) -- *)
let rdi_fact  = ch_find "read RDI" poEc;;                (* RDI = sptr (ENTRY post) *)
let rsi_pre   = ch_find "read RSI" peMc;;                (* RSI = mptr *)
let ymm1_pack = ch_find "YMM1_SSE" poEc;;                (* ABEF_PACK(q0..) *)
let ymm2_pack = ch_find "YMM2_SSE" poEc;;                (* CDGH_PACK(q0..) *)
let msg_reads = filter (fun c -> ch_contains (string_of_term c) "read (memory"
                   && ch_contains (string_of_term c) "mptr") peMc;;
let k_reads = filter (fun c -> ch_contains (string_of_term c) "read (memory"
                 && (ch_contains (string_of_term c) "bytes128 kptr)"
                     || ch_contains (string_of_term c) "18446744073709551")) peCc;;

Printf.printf "S042_CH counts: msg_reads=%d k_reads=%d\n%!"
  (List.length msg_reads) (List.length k_reads);;

(* -- composed PRE = ENTRY.pre + {RSI=mptr, 4 msg reads, 5 K reads} -- *)
let pre_lam = mk_abs(sv, list_mk_conj (peEc @ [rsi_pre] @ msg_reads @ k_reads));;

(* -- composed POST = CRYPTO.post + {RDI=sptr} -- *)
let post_lam = mk_abs(sv, list_mk_conj (poCc @ [rdi_fact]));;

(* -- composed FRAME = union ENTRY {YMM0/1/2/7/8} + MSG {YMM3/4/5/6} +          *)
(*    CRYPTO {RSI,YMM0..7,9,10,flags} -- *)
let comp_frame =
 `MAYCHANGE [RIP; RSI] ,,
  MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM5_SSE;
             YMM6_SSE; YMM7_SSE; YMM8_SSE; YMM9_SSE; YMM10_SSE] ,,
  MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;

(* -- hyps: ENTRY's aligned(kptr+384) + CRYPTO's 4 neg-disp aligned -- *)
let comp_hyps = list_mk_conj
 [`aligned 16 (word_add (kptr:int64) (word 384))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551488))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551520))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551552))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551584))`];;

let ens_head = rator(rator(rator(snd(dest_imp(snd(strip_forall(concl
                 SHA256_COMPRESS_HW_ENTRY_REPACK)))))));;
let mk_ensures p q c = mk_comb(mk_comb(mk_comb(ens_head,p),q),c);;
let bvars = [`pc:num`;`kbase:num`;`kptr:int64`;`sptr:int64`;`mptr:int64`;
             `q0:int128`;`q1:int128`;`m0:int128`;`m1:int128`;`m2:int128`;`m3:int128`;
             `kq0:int128`;`kq1:int128`;`kq2:int128`;`kq3:int128`;`kq4:int128`];;
let comp_concl =
  list_mk_forall(bvars, mk_imp(comp_hyps, mk_ensures pre_lam post_lam comp_frame));;

(* -- seams (minus bytes_loaded + read RIP) -- *)
let keep c = not(ch_contains (string_of_term c) "bytes_loaded")
             && not(ch_contains (string_of_term c) "read RIP");;
let core cs = filter keep cs;;
(* seam1@0x38 = MSGLOAD.pre-core + {YMM1,YMM2 (ENTRY), 5 K reads, RDI=sptr} *)
let seamQ1 = mk_abs(sv,
  list_mk_conj (core peMc @ [ymm1_pack; ymm2_pack] @ k_reads @ [rdi_fact]));;
(* seam2@0x50 = CRYPTO.pre-core + {RDI=sptr} *)
let seamQ2 = mk_abs(sv, list_mk_conj (core peCc @ [rdi_fact]));;

Printf.printf "S042_CH concl built\n%!";;

let SHA256_COMPRESS_HW_CORE_HEAD = prove
 (comp_concl,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x38` seamQ1 THEN CONJ_TAC THENL
   [(* leg 1: ENTRY_REPACK[mask:=lit] *)
    MP_TAC entry_i THEN ASM_REWRITE_TAC[] THEN
    ENSURES_SUBLEMMA_TAC execup "s" "s'" THEN ASM_REWRITE_TAC[];
    ENSURES_SEQUENCE_TAC `pc + 0x50` seamQ2 THEN CONJ_TAC THENL
     [(* leg 2: HEAD_MSGLOAD0 *)
      MP_TAC msg_i THEN ASM_REWRITE_TAC[] THEN
      ENSURES_SUBLEMMA_TAC execup "s" "s'" THEN ASM_REWRITE_TAC[];
      (* leg 3: CORE_HEAD_CRYPTO[l:=state words, EL-reduced] *)
      MP_TAC(REWRITE_RULE[SOME_FLAGS] crypto_i) THEN ASM_REWRITE_TAC[] THEN
      ENSURES_SUBLEMMA_TAC execup "s" "s'" THEN ASM_REWRITE_TAC[]]]);;

Printf.printf "S042_CORE_HEAD hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_CORE_HEAD))
  (List.length (frees (concl SHA256_COMPRESS_HW_CORE_HEAD)));;
Printf.printf "S042_COREHEAD_DONE\n%!";;

(* ========================================================================= *)
(* Session 045 -- opaque SPEC-STEP for the disp32 steady groups g8..g12.      *)
(* The s044 SPEC_STEP_R{0..3} lemmas cover only g4-g7 (disp0/disp8, PCs        *)
(* 0xf4-0x1a7, K@kptr+{0,32,64,96}).  The steady round-engine body also runs   *)
(* through g8..g12 (disp32 K-loads, PCs 0x1a7-0x297, K@kptr+{128..288}).       *)
(* Each is the SAME opaque per-group advance (compress_rounds 4g->4g+4,        *)
(* constant-size seam) as its rotation template FULL_S_R{g mod 4}, so we       *)
(* RETARGET the committed SPEC_STEP_R{r} conclusion to the disp32 PCs/K-        *)
(* offsets (reusing the s038 retarget helpers) and REPLAY the identical INST-   *)
(* fold-ACCEPT tactic, but INSTing the disp32 raw atom FULL_S_G{n}.  The ring    *)
(* INST map and the R0_YMM{4,5,6}/CR4_SPEC_STEP_WWIN folds are stated over       *)
(* schedule OFFSETS (register-agnostic), so they apply verbatim.  All hyp-free.  *)
(* g8=r0 g9=r1 g10=r2 g11=r3 g12=r0 (period-4).  Soundness inherits from the    *)
(* reviewed FULL_S_G{n} atoms (ACCEPT_TAC = syntactic identity).                 *)
(* ========================================================================= *)
(* --- the 4 committed rotation templates + their PCs/K-disps --- *)
let specstep_tmpl = [| SHA256_COMPRESS_HW_SPEC_STEP_R0;
                       SHA256_COMPRESS_HW_SPEC_STEP_R1;
                       SHA256_COMPRESS_HW_SPEC_STEP_R2;
                       SHA256_COMPRESS_HW_SPEC_STEP_R3 |];;
let specstep_tmpl_pcs  = [| (0xf4,0x120); (0x120,0x14d); (0x14d,0x17a); (0x17a,0x1a7) |];;
let specstep_tmpl_disp = [| (0,32); (32,64); (64,96); (96,128) |];;

(* ring INST map (replacement, atom-binder), per rotation.  The K-quad     *)
(* binder differs by rotation to match FULL_S_R{r}/FULL_S_G{n}: r0->kq,     *)
(* r1->kq1, r2->kq2, r3->kq3 (verified from FULL_S_G8/G9 binders).          *)
let kconsts = `WQUAD (EL (4*g) sha256_constants) (EL (4*g+1) sha256_constants)
                     (EL (4*g+2) sha256_constants) (EL (4*g+3) sha256_constants):int128`;;
let l_repl = `sha256_compress_rounds m (st:int32 list) (4*g):int32 list`;;
let w0=`WWIN m (4*g):int128` and wm4=`WWIN m (4*g-4):int128`
and p12=`PADP m (4*g-12):int128` and m8=`MSG1P m (4*g-8):int128`;;
let specstep_ringmap r =
  let base = match r with
   | 0 -> [w0,`a3:int128`; p12,`a4:int128`; m8,`a5:int128`; wm4,`a6:int128`; kconsts,`kq:int128`]
   | 1 -> [wm4,`a3:int128`; w0,`a4:int128`; p12,`a5:int128`; m8,`a6:int128`; kconsts,`kq1:int128`]
   | 2 -> [m8,`a3:int128`; wm4,`a4:int128`; w0,`a5:int128`; p12,`a6:int128`; kconsts,`kq2:int128`]
   | _ -> [p12,`a3:int128`; m8,`a4:int128`; wm4,`a5:int128`; w0,`a6:int128`; kconsts,`kq3:int128`] in
  base @ [l_repl,`l:int32 list`];;

(* retarget SPEC_STEP_R{r}'s conclusion to a disp32 group's PCs/K-offsets. *)
let retarget_specstep r (ge,gx) (gkc,gkn) =
  let (te,tx) = specstep_tmpl_pcs.(r) and (tkc,tkn) = specstep_tmpl_disp.(r) in
  let subl = [ pcoff_038 ge, pcoff_038 te; pcoff_038 gx, pcoff_038 tx;
               b128_038 gkc, b128_038 tkc; b128_038 gkn, b128_038 tkn;
               aligned_038 gkc, aligned_038 tkc ] in
  retarget_concl_038 subl specstep_tmpl.(r);;

let specstep_tac r atom =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`m:int32 list`;`g:num`] R0_YMM4) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`m:int32 list`;`g:num`] R0_YMM5) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`m:int32 list`;`g:num`] R0_YMM6) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(INST (specstep_ringmap r) (SPEC_ALL atom)) THEN
  ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[CR4_SPEC_STEP_WWIN] THEN
  DISCH_THEN ACCEPT_TAC;;

let gen_specstep r atom (ge,gx) (gkc,gkn) =
  prove(retarget_specstep r (ge,gx) (gkc,gkn), specstep_tac r atom);;

(* --- prove g8 first as a probe (r=0, PC 0x1a7->0x1d7, K@128/160) --- *)
let SHA256_COMPRESS_HW_SPEC_STEP_G8 =
  gen_specstep 0 SHA256_COMPRESS_HW_GROUP4_FULL_S_G8 (0x1a7,0x1d7) (128,160);;
Printf.printf "S045_SPEC_STEP_G8 hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_SPEC_STEP_G8))
  (List.length(frees(concl SHA256_COMPRESS_HW_SPEC_STEP_G8)));;
Printf.printf "S045_G8_PROBE_DONE\n%!";;

(* --- g9..g12: r=1,2,3,0.  PCs & K-disps from gen_group_038 rows. --- *)
let SHA256_COMPRESS_HW_SPEC_STEP_G9 =
  gen_specstep 1 SHA256_COMPRESS_HW_GROUP4_FULL_S_G9 (0x1d7,0x207) (160,192);;
Printf.printf "S045_SPEC_STEP_G9 hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_SPEC_STEP_G9))
  (List.length(frees(concl SHA256_COMPRESS_HW_SPEC_STEP_G9)));;

let SHA256_COMPRESS_HW_SPEC_STEP_G10 =
  gen_specstep 2 SHA256_COMPRESS_HW_GROUP4_FULL_S_G10 (0x207,0x237) (192,224);;
Printf.printf "S045_SPEC_STEP_G10 hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_SPEC_STEP_G10))
  (List.length(frees(concl SHA256_COMPRESS_HW_SPEC_STEP_G10)));;

let SHA256_COMPRESS_HW_SPEC_STEP_G11 =
  gen_specstep 3 SHA256_COMPRESS_HW_GROUP4_FULL_S_G11 (0x237,0x267) (224,256);;
Printf.printf "S045_SPEC_STEP_G11 hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_SPEC_STEP_G11))
  (List.length(frees(concl SHA256_COMPRESS_HW_SPEC_STEP_G11)));;

let SHA256_COMPRESS_HW_SPEC_STEP_G12 =
  gen_specstep 0 SHA256_COMPRESS_HW_GROUP4_FULL_S_G12 (0x267,0x297) (256,288);;
Printf.printf "S045_SPEC_STEP_G12 hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_SPEC_STEP_G12))
  (List.length(frees(concl SHA256_COMPRESS_HW_SPEC_STEP_G12)));;
Printf.printf "S045_SPEC_STEP_G8_G12_DONE\n%!";;

(* ========================================================================= *)
(* Session 045 -- HEAD-SEAM SPEC FOLDS: convert CORE_HEAD's concrete POST @   *)
(* pc+0xf4 into the opaque SPEC_STEP_R0 (g=4) PRE form.  CORE_HEAD carries     *)
(*   crypto = CR4(CR4(CR4(CR4 st (add kq0 b0))(add kq1 b1))(add kq2 b2))       *)
(*                 (add kq3 b3)                                                *)
(*   ring  YMM3 = msg2(simd4 add (msg1 b0 b1)(palignr b3 b2)) b3               *)
(*         YMM4 = simd4 add (msg1 b1 b2)(palignr YMM3 b3)                      *)
(*         YMM5 = msg1 b2 b3      YMM6 = b3                                     *)
(* where b_i = usimd4 word_bytereverse m_i (the loaded big-endian msg quads).  *)
(* SPEC_STEP_R0 @ g=4 wants  crypto = compress_rounds m st 16, YMM3 = WWIN 16, *)
(* YMM4 = PADP 4, YMM5 = MSG1P 8, YMM6 = WWIN 12.  These folds discharge each  *)
(* given the message base-case bindings  b_i = WWIN m (4*i)  and the K-const   *)
(* bindings  kq_i = WQUAD (EL (4i) consts..)  (supplied by the spec-connection *)
(* caller: WWIN m (4i) for 4i<16 is just the raw 4-word message quad, since    *)
(* sha256_msg_schedule m t = EL t m for t<16).  The crypto fold chains four    *)
(* CR4_SPEC_STEP_WWIN steps (g=0,1,2,3) off compress_rounds m st 0 = st.       *)
(* ========================================================================= *)

let SHA256_COMPRESS_HW_HEAD_CRYPTO_FOLD = prove
 (`!(m:int32 list) (st:int32 list) kq0 kq1 kq2 kq3 b0 b1 b2 b3.
      kq0 = WQUAD (EL 0 sha256_constants) (EL 1 sha256_constants)
                  (EL 2 sha256_constants) (EL 3 sha256_constants) /\
      kq1 = WQUAD (EL 4 sha256_constants) (EL 5 sha256_constants)
                  (EL 6 sha256_constants) (EL 7 sha256_constants) /\
      kq2 = WQUAD (EL 8 sha256_constants) (EL 9 sha256_constants)
                  (EL 10 sha256_constants) (EL 11 sha256_constants) /\
      kq3 = WQUAD (EL 12 sha256_constants) (EL 13 sha256_constants)
                  (EL 14 sha256_constants) (EL 15 sha256_constants) /\
      b0 = WWIN m 0 /\ b1 = WWIN m 4 /\ b2 = WWIN m 8 /\ b3 = WWIN m 12
      ==> CR4 (CR4 (CR4 (CR4 st (simd4 word_add kq0 b0))
                        (simd4 word_add kq1 b1))
                   (simd4 word_add kq2 b2))
              (simd4 word_add kq3 b3)
          = sha256_compress_rounds m st 16`,
  let redu = CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV) in
  let i0 = redu(SPECL [`m:int32 list`;`st:int32 list`;`0`] CR4_SPEC_STEP_WWIN)
  and i1 = redu(SPECL [`m:int32 list`;`st:int32 list`;`1`] CR4_SPEC_STEP_WWIN)
  and i2 = redu(SPECL [`m:int32 list`;`st:int32 list`;`2`] CR4_SPEC_STEP_WWIN)
  and i3 = redu(SPECL [`m:int32 list`;`st:int32 list`;`3`] CR4_SPEC_STEP_WWIN) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(funpow 4 (RATOR_CONV o RAND_CONV)
                       (GEN_REWRITE_CONV I [GSYM(REWRITE_CONV[sha256_compress_rounds]
                           `sha256_compress_rounds m st 0`)]))) THEN
  REWRITE_TAC[i0] THEN REWRITE_TAC[i1] THEN REWRITE_TAC[i2] THEN REWRITE_TAC[i3]);;
Printf.printf "S045_HEAD_CRYPTO_FOLD hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_HEAD_CRYPTO_FOLD))
  (List.length(frees(concl SHA256_COMPRESS_HW_HEAD_CRYPTO_FOLD)));;

let SHA256_COMPRESS_HW_HEAD_YMM3 = prove
 (`!(m:int32 list) b0 b1 b2 b3.
      b0 = WWIN m 0 /\ b1 = WWIN m 4 /\ b2 = WWIN m 8 /\ b3 = WWIN m 12
      ==> sha256_msg2
            (simd4 word_add (sha256_msg1 b0 b1)
               (word_subword (word_ushr
                  ((word_join:int128->int128->256 word) b3 b2) (8*4)) (0,128)))
            b3
          = WWIN m 16`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM(SPECL[`m:int32 list`;`0`] PADP); MSG1_WWIN; PADP] THEN
  MP_TAC(SPECL[`m:int32 list`;`0`] WRING_WWIN) THEN
  REWRITE_TAC[PADP; MSG1P] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;
Printf.printf "S045_HEAD_YMM3 hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_HEAD_YMM3))
  (List.length(frees(concl SHA256_COMPRESS_HW_HEAD_YMM3)));;

let SHA256_COMPRESS_HW_HEAD_YMM4 = prove
 (`!(m:int32 list) b0 b1 b2 b3.
      b0 = WWIN m 0 /\ b1 = WWIN m 4 /\ b2 = WWIN m 8 /\ b3 = WWIN m 12
      ==> simd4 word_add (sha256_msg1 b1 b2)
            (word_subword (word_ushr
               ((word_join:int128->int128->256 word)
                  (sha256_msg2
                     (simd4 word_add (sha256_msg1 b0 b1)
                        (word_subword (word_ushr
                           ((word_join:int128->int128->256 word) b3 b2) (8*4)) (0,128)))
                     b3)
                  b3)
               (8*4)) (0,128))
          = PADP m 4`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL[`m:int32 list`;`b0:int128`;`b1:int128`;`b2:int128`;`b3:int128`]
              SHA256_COMPRESS_HW_HEAD_YMM3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[PADP; MSG1P] THEN CONV_TAC NUM_REDUCE_CONV);;
Printf.printf "S045_HEAD_YMM4 hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_HEAD_YMM4))
  (List.length(frees(concl SHA256_COMPRESS_HW_HEAD_YMM4)));;

let SHA256_COMPRESS_HW_HEAD_YMM5 = prove
 (`!(m:int32 list) b2 b3.
      b2 = WWIN m 8 /\ b3 = WWIN m 12 ==> sha256_msg1 b2 b3 = MSG1P m 8`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MSG1P] THEN CONV_TAC NUM_REDUCE_CONV);;
Printf.printf "S045_HEAD_YMM5 hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_HEAD_YMM5))
  (List.length(frees(concl SHA256_COMPRESS_HW_HEAD_YMM5)));;
Printf.printf "S045_HEAD_SEAM_FOLDS_DONE\n%!";;

(* ========================================================================= *)
(* Session 046 -- THE HEAD-SEAM BYTESWAP BRIDGE PROPER (the real gap the      *)
(* committed head folds are CONDITIONAL on).  HEAD_CRYPTO_FOLD/HEAD_YMM3/4/5   *)
(* take a hypothesis  b_i = WWIN m (4*i)  where b_i = usimd4 word_bytereverse  *)
(* m_i is CORE_HEAD's byteswapped head quad (m_i the raw movdqu'd memory       *)
(* operand).  This block proves that hypothesis from the hardware register     *)
(* contents: byteswapping the loaded quad reverses each 32-bit lane back to    *)
(* the spec word, and the schedule-window base case (t<16) collapses           *)
(* sha256_msg_schedule m t to EL t m -- so the loaded/byteswapped head quad IS *)
(* the schedule window WWIN m (4*i).                                           *)
(*                                                                           *)
(* Memory convention (lifted from nohw SHA256_BLOCK_NOHW_HEAD16_ABS, where     *)
(* read (bytes32 ..) = word_bytereverse (EL t m)): the raw 128-bit message     *)
(* quad m_i has lanes word_bytereverse (EL (4i+j) m), j=0..3, so m has the      *)
(* big-endian / spec dword ordering and each raw lane is its byteswap.  This    *)
(* convention is discharged by the Phase-6 spec-connection caller that ties     *)
(* the movdqu operands to the spec message m.                                  *)
(* ========================================================================= *)

(* Spec base case: for t < 16 the schedule word is just the raw message word.  *)
let SHA256_MSCH_LT16 = prove
 (`!(m:int32 list) t. t < 16 ==> sha256_msg_schedule m t = EL t m`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [sha256_msg_schedule] THEN
  ASM_REWRITE_TAC[]);;
Printf.printf "S046_MSCH_LT16 hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_MSCH_LT16)) (List.length(frees(concl SHA256_MSCH_LT16)));;

(* usimd4 word_bytereverse is an involution on int128 (each 32-bit lane        *)
(* byte-reversed twice is the identity).  Reusable Route-A building block.     *)
let USIMD4_BYTEREVERSE_INVOL = prove
 (`!x:int128. usimd4 word_bytereverse (usimd4 word_bytereverse x) = x`,
  GEN_TAC THEN REWRITE_TAC[usimd4; usimd2] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC WORD_BLAST);;
Printf.printf "S046_USIMD4_BYTEREVERSE_INVOL hyps=%d frees=%d\n%!"
  (List.length(hyp USIMD4_BYTEREVERSE_INVOL))
  (List.length(frees(concl USIMD4_BYTEREVERSE_INVOL)));;

(* THE BRIDGE: byteswapping the raw head quad (lanes = wbr(EL (4i+j) m)) folds  *)
(* to the schedule window WWIN m (4*i), for the four head quads i=0..3.         *)
let SHA256_COMPRESS_HW_HEAD_MSG_BRIDGE = prove
 (`!(m:int32 list) i. i < 4
     ==> usimd4 word_bytereverse
           (WQUAD (word_bytereverse (EL (4*i) m)) (word_bytereverse (EL (4*i+1) m))
                  (word_bytereverse (EL (4*i+2) m)) (word_bytereverse (EL (4*i+3) m)))
         = WWIN m (4*i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WWIN] THEN
  SUBGOAL_THEN `4*i < 16 /\ (4*i)+1 < 16 /\ (4*i)+2 < 16 /\ (4*i)+3 < 16`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SHA256_MSCH_LT16] THEN
  REWRITE_TAC[usimd4; usimd2; WQUAD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC WORD_BLAST);;
Printf.printf "S046_HEAD_MSG_BRIDGE hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_HEAD_MSG_BRIDGE))
  (List.length(frees(concl SHA256_COMPRESS_HW_HEAD_MSG_BRIDGE)));;
Printf.printf "S046_HEAD_MSG_BRIDGE_DONE\n%!";;

(* ========================================================================= *)
(* Session 046 -- CORE_HEAD_ABS: CORE_HEAD's POST @ pc+0xf4 restated in the   *)
(* OPAQUE SPEC form (crypto = sha256_compress_rounds m st 16; ring occupants  *)
(* = WWIN/PADP/MSG1P windows), which is EXACTLY SPEC_STEP_R0[g:=4]'s PRE.      *)
(* This closes the head seam: the monolith chains CORE_HEAD_ABS -> the steady  *)
(* SPEC_STEP layer with only the trivial 16 = 4*4 normalization.               *)
(*                                                                           *)
(* Derivation (nohw HEAD16_ABS pattern): specialize CORE_HEAD's raw memory     *)
(* quads to their spec forms -- message quad m_i := WQUAD(wbr(EL(4i+j)m)) (the *)
(* nohw byteswap convention), K quad kq_i := WQUAD(EL(4i+j)consts) -- then      *)
(* rewrite the byteswapped POST occupants via HEAD_MSG_BRIDGE (b_i = WWIN(4i)) *)
(* + the committed head folds HEAD_CRYPTO_FOLD/YMM3/4/5.  The working state is  *)
(* st = [q0 lanes; q1 lanes] (the loaded ABEF/CDGH state).                     *)
(*                                                                           *)
(* FOLD-ORDER TRAP: HEAD_YMM4 must fire BEFORE HEAD_YMM3, else HEAD_YMM3       *)
(* rewrites the inner msg2 to WWIN 16 *inside* YMM4's palignr and breaks       *)
(* HEAD_YMM4's LHS match (targeted GEN_REWRITE for ymm4 first, then the rest). *)
(* ========================================================================= *)

let SHA256_COMPRESS_HW_CORE_HEAD_ABS =
  let strip_atom th =
    let bod = snd(strip_forall(concl th)) in
    let ens = if is_imp bod then snd(dest_imp bod) else bod in
    let l,c = dest_comb ens in let l2,q = dest_comb l in
    let _,p = dest_comb l2 in (p,q,c) in
  let e j i = mk_comb(`word_bytereverse:int32->int32`,
      list_mk_comb(`EL:num->(int32)list->int32`,[mk_small_numeral(4*i+j);`m:int32 list`])) in
  let rawquad i = list_mk_comb(`WQUAD:int32->int32->int32->int32->int128`,
                    [e 0 i;e 1 i;e 2 i;e 3 i]) in
  let kc j i = list_mk_comb(`EL:num->(int32)list->int32`,
      [mk_small_numeral(4*i+j);`sha256_constants:int32 list`]) in
  let kquad i = list_mk_comb(`WQUAD:int32->int32->int32->int32->int128`,
                  [kc 0 i;kc 1 i;kc 2 i;kc 3 i]) in
  let subs = [ rawquad 0,`m0:int128`; rawquad 1,`m1:int128`;
               rawquad 2,`m2:int128`; rawquad 3,`m3:int128`;
               kquad 0,`kq0:int128`; kquad 1,`kq1:int128`;
               kquad 2,`kq2:int128`; kquad 3,`kq3:int128` ] in
  let headI = INST subs (SPEC_ALL SHA256_COMPRESS_HW_CORE_HEAD) in
  let bfold i =
    let br = SPECL [`m:int32 list`; mk_small_numeral i] SHA256_COMPRESS_HW_HEAD_MSG_BRIDGE in
    let br = MP br (ARITH_RULE(mk_comb(mk_comb(`(<):num->num->bool`,mk_small_numeral i),`4`))) in
    CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV) br in
  let bthms = map bfold [0;1;2;3] in
  let stlist = `[word_subword (q0:int128) (0,32); word_subword q0 (32,32);
                 word_subword q0 (64,32); word_subword q0 (96,32);
                 word_subword (q1:int128) (0,32); word_subword q1 (32,32);
                 word_subword q1 (64,32); word_subword q1 (96,32)] : int32 list` in
  let wwin i = list_mk_comb(`WWIN:(int32)list->num->int128`,
                 [`m:int32 list`;mk_small_numeral(4*i)]) in
  let cryptofold =
    let th = INST ([ stlist,`st:int32 list` ] @
                   (map (fun i -> kquad i, mk_var("kq"^string_of_int i,`:int128`)) [0;1;2;3]) @
                   (map (fun i -> wwin i, mk_var("b"^string_of_int i,`:int128`)) [0;1;2;3]))
              (SPEC_ALL SHA256_COMPRESS_HW_HEAD_CRYPTO_FOLD) in
    MP th (end_itlist CONJ (map REFL ((map kquad [0;1;2;3]) @ (map wwin [0;1;2;3])))) in
  let ymm3fold =
    let th = INST (map (fun i -> wwin i, mk_var("b"^string_of_int i,`:int128`)) [0;1;2;3])
              (SPEC_ALL SHA256_COMPRESS_HW_HEAD_YMM3) in
    MP th (end_itlist CONJ (map (fun i -> REFL(wwin i)) [0;1;2;3])) in
  let ymm4fold =
    let th = INST (map (fun i -> wwin i, mk_var("b"^string_of_int i,`:int128`)) [0;1;2;3])
              (SPEC_ALL SHA256_COMPRESS_HW_HEAD_YMM4) in
    MP th (end_itlist CONJ (map (fun i -> REFL(wwin i)) [0;1;2;3])) in
  let ymm5fold =
    let th = INST [wwin 2,`b2:int128`; wwin 3,`b3:int128`]
              (SPEC_ALL SHA256_COMPRESS_HW_HEAD_YMM5) in
    MP th (CONJ (REFL(wwin 2)) (REFL(wwin 3))) in
  let headB   = REWRITE_RULE bthms headI in
  let headB4  = GEN_REWRITE_RULE (RAND_CONV o TOP_DEPTH_CONV) [ymm4fold] headB in
  GEN_ALL(REWRITE_RULE [cryptofold; ymm3fold; ymm5fold] headB4);;

Printf.printf "S046_CORE_HEAD_ABS hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_CORE_HEAD_ABS))
  (List.length(frees(concl SHA256_COMPRESS_HW_CORE_HEAD_ABS)));;
Printf.printf "S046_CORE_HEAD_ABS_DONE\n%!";;

(* ========================================================================= *)
(* Session 049 -- MONOLITH CHECKPOINT A: head ; R0[g:=4] ; R1[g:=5],          *)
(* pc+0x07 -> pc+0x14d.  The first committed partial compose (orchestrator     *)
(* mandate: land checkpoints incrementally).  Validates live-chaining of the   *)
(* two hardest seam classes -- head (non-reflexive: kq4 concrete + YMM9/10/RDI *)
(* riders) and steady K-window carry (two adjacent K quads ride RO frame).     *)
(* ONE prove, nested ENSURES_SEQUENCE, all legs leaf atoms (s042: sublemma     *)
(* can't HO-unify a giant composite POST).  Ported from s049-pilotfix.ml       *)
(* (the fixed s048 pilot: 3<=g reduced to T via NUM_LE_CONV else ENSURES_      *)
(* SUBLEMMA_THM "No match").                                                   *)
(* ========================================================================= *)
let strip_atom th =
  let bod = snd(strip_forall(concl th)) in
  let ens = if is_imp bod then snd(dest_imp bod) else bod in
  let l,c = dest_comb ens in let l2,q = dest_comb l in
  let _,p = dest_comb l2 in (p,q,c);;
let ens_of th = let bod = snd(strip_forall(concl th)) in
  if is_imp bod then snd(dest_imp bod) else bod;;
let conjs_of_lam q = let s,body = dest_abs q in s, conjuncts body;;
let contains s sub =
  let ls=String.length s and lsub=String.length sub in
  let rec go i = i+lsub<=ls && (String.sub s i lsub = sub || go(i+1)) in go 0;;
let findc sub cs = find (fun c -> contains (string_of_term c) sub) cs;;
let nred_rule = CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV
                          THENC DEPTH_CONV NUM_SUB_CONV THENC DEPTH_CONV NUM_LE_CONV);;
let keepseam c = not(contains (string_of_term c) "bytes_loaded")
                 && not(contains (string_of_term c) "read RIP");;
let sv = `s:x86state`;;
let rebase lam = let s,cs = conjs_of_lam lam in map (vsubst[sv,s]) cs;;

let stlist = `[word_subword (q0:int128) (0,32); word_subword q0 (32,32);
               word_subword q0 (64,32); word_subword q0 (96,32);
               word_subword (q1:int128) (0,32); word_subword q1 (32,32);
               word_subword q1 (64,32); word_subword q1 (96,32)] : int32 list`;;
let kquad n =
  let el j = list_mk_comb(`EL:num->(int32)list->int32`,
               [mk_small_numeral(4*n+j);`sha256_constants:int32 list`]) in
  list_mk_comb(`WQUAD:int32->int32->int32->int32->int128`,[el 0;el 1;el 2;el 3]);;

let steady_leg th g =
  let sp = SPECL [`pc:num`;`kbase:num`;`kptr:int64`;`m:int32 list`;stlist;
                  mk_small_numeral g] th in
  REWRITE_RULE[] (nred_rule (SPEC (kquad (g+1)) sp));;

let head = INST [kquad 4, `kq4:int128`] (SPEC_ALL SHA256_COMPRESS_HW_CORE_HEAD_ABS);;
let r0 = steady_leg SHA256_COMPRESS_HW_SPEC_STEP_R0 4;;
let r1 = steady_leg SHA256_COMPRESS_HW_SPEC_STEP_R1 5;;

let (pH,qH,fH) = strip_atom head;;
let (pr0,qr0,fr0) = strip_atom r0;;
let (pr1,qr1,fr1) = strip_atom r1;;
let pHc = rebase pH;;
let qHc = rebase qH;;
let pr0c = rebase pr0;;
let pr1c = rebase pr1;;
let qr1c = rebase qr1;;

let ymm9 = findc "YMM9_SSE" qHc;;
let ymm10 = findc "YMM10_SSE" qHc;;
let rdi = findc "read RDI" qHc;;
let kq5 = findc "(word 32)" pr0c;;   (* r0's kqNEXT @+32 = kquad5 *)
let kq6 = findc "(word 64)" pr1c;;   (* r1's kqNEXT @+64 = kquad6 *)

let core cs = filter keepseam cs;;
let seamQ1 = mk_abs(sv, list_mk_conj (core pr0c @ [ymm9;ymm10;rdi;kq6]));;
let seamQ2 = mk_abs(sv, list_mk_conj (core pr1c @ [ymm9;ymm10;rdi]));;
let pre_lam = mk_abs(sv, list_mk_conj (pHc @ [kq5; kq6]));;
let post_lam = mk_abs(sv, list_mk_conj (qr1c @ [ymm9;ymm10;rdi]));;

let ens_head = rator(rator(rator(ens_of head)));;
let mk_ensures p q c = mk_comb(mk_comb(mk_comb(ens_head,p),q),c);;
let bvars = [`pc:num`;`kbase:num`;`kptr:int64`;`m:int32 list`;
             `q0:int128`;`q1:int128`;`mptr:int64`;`sptr:int64`];;
let comp_hyps = list_mk_conj
 [`aligned 16 (kptr:int64)`;
  `aligned 16 (word_add (kptr:int64) (word 384))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551488))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551520))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551552))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551584))`];;
let comp_concl = list_mk_forall(bvars, mk_imp(comp_hyps, mk_ensures pre_lam post_lam fH));;
Printf.printf "PILOT concl built.\n%!";;

let SHA256_COMPRESS_HW_MONO_A = prove
 (comp_concl,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  SUBGOAL_THEN `aligned 16 (word_add (kptr:int64) (word 32))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORMALIZE_ALIGNED_WORD_CONV
       `aligned 16 (word_add (kptr:int64) (word 32))`]; ALL_TAC] THEN
  SUBGOAL_THEN `aligned 16 (word_add (kptr:int64) (word 64))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORMALIZE_ALIGNED_WORD_CONV
       `aligned 16 (word_add (kptr:int64) (word 64))`]; ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `pc + 0xf4` seamQ1 THEN CONJ_TAC THENL
   [MP_TAC(REWRITE_RULE[SOME_FLAGS] head) THEN ASM_REWRITE_TAC[] THEN
    ENSURES_SUBLEMMA_TAC execup "s" "s'" THEN ASM_REWRITE_TAC[];
    ENSURES_SEQUENCE_TAC `pc + 0x120` seamQ2 THEN CONJ_TAC THENL
     [MP_TAC(REWRITE_RULE[SOME_FLAGS] r0) THEN ASM_REWRITE_TAC[] THEN
      ENSURES_SUBLEMMA_TAC execup "s" "s'" THEN ASM_REWRITE_TAC[];
      MP_TAC(REWRITE_RULE[SOME_FLAGS] r1) THEN ASM_REWRITE_TAC[] THEN
      ENSURES_SUBLEMMA_TAC execup "s" "s'" THEN ASM_REWRITE_TAC[]]]);;

Printf.printf "S049_MONO_A hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_MONO_A))
  (List.length(frees(concl SHA256_COMPRESS_HW_MONO_A)));;
Printf.printf "S049_MONO_A_DONE\n%!";;

(* ========================================================================= *)
(* Session 049 -- MONOLITH CHECKPOINT B: head ; R0[g4] ; R1[g5] ; R2[g6] ;    *)
(* R3[g7], pc+0x07 -> pc+0x1a7.  Extends MONO_A by two steady legs = a full    *)
(* period-4 steady cycle after the head.  Same K-window frame-carry as         *)
(* CORE_4GROUP: composed PRE lists kq5..kq8 (RO, ride the memory-untouched     *)
(* frame); each seam re-states the K quads downstream legs still need + the     *)
(* YMM9/10/RDI riders (no steady frame touches them).  hyps=0, first try.       *)
(* ========================================================================= *)
(* S049 MONO_B: head ; R0[g4] ; R1[g5] ; R2[g6] ; R3[g7], pc+0x07 -> pc+0x1a7.
   Extends the proven MONO_A pilot by two steady legs (R2,R3), a full period-4
   steady cycle after the head.  Same K-window frame-carry as CORE_4GROUP:
   composed PRE lists kq5..kq8 (RO, ride the memory-untouched frame); each seam
   re-states the K quads downstream legs still need + YMM9/10/RDI riders.
   ONE prove, nested ENSURES_SEQUENCE, all legs leaf atoms. *)

let strip_atom th =
  let bod = snd(strip_forall(concl th)) in
  let ens = if is_imp bod then snd(dest_imp bod) else bod in
  let l,c = dest_comb ens in let l2,q = dest_comb l in
  let _,p = dest_comb l2 in (p,q,c);;
let ens_of th = let bod = snd(strip_forall(concl th)) in
  if is_imp bod then snd(dest_imp bod) else bod;;
let conjs_of_lam q = let s,body = dest_abs q in s, conjuncts body;;
let contains s sub =
  let ls=String.length s and lsub=String.length sub in
  let rec go i = i+lsub<=ls && (String.sub s i lsub = sub || go(i+1)) in go 0;;
let findc sub cs = find (fun c -> contains (string_of_term c) sub) cs;;
(* robust K-read matcher: needs BOTH bytes128 AND "(word off)" -- avoids the
   bytes128->"128" clash and word_subword (64,32) clash. *)
let is_kread off c =
  is_eq c && contains (string_of_term c) "bytes128"
          && contains (string_of_term c) ("(word " ^ off ^ ")");;
let kread_in off cs = find (is_kread off) cs;;
let nred_rule = CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV
                          THENC DEPTH_CONV NUM_SUB_CONV THENC DEPTH_CONV NUM_LE_CONV);;
let keepseam c = not(contains (string_of_term c) "bytes_loaded")
                 && not(contains (string_of_term c) "read RIP");;
let sv = `s:x86state`;;
let rebase lam = let s,cs = conjs_of_lam lam in map (vsubst[sv,s]) cs;;

let stlist = `[word_subword (q0:int128) (0,32); word_subword q0 (32,32);
               word_subword q0 (64,32); word_subword q0 (96,32);
               word_subword (q1:int128) (0,32); word_subword q1 (32,32);
               word_subword q1 (64,32); word_subword q1 (96,32)] : int32 list`;;
let kquad n =
  let el j = list_mk_comb(`EL:num->(int32)list->int32`,
               [mk_small_numeral(4*n+j);`sha256_constants:int32 list`]) in
  list_mk_comb(`WQUAD:int32->int32->int32->int32->int128`,[el 0;el 1;el 2;el 3]);;

(* one steady leg: SPECL the 6 named binders + SPEC the trailing kq binder to
   kquad(g+1), then reduce the concrete arithmetic (incl. 3<=g -> T). *)
let steady_leg th g =
  let sp = SPECL [`pc:num`;`kbase:num`;`kptr:int64`;`m:int32 list`;stlist;
                  mk_small_numeral g] th in
  REWRITE_RULE[] (nred_rule (SPEC (kquad (g+1)) sp));;

let head = INST [kquad 4, `kq4:int128`] (SPEC_ALL SHA256_COMPRESS_HW_CORE_HEAD_ABS);;
let r0 = steady_leg SHA256_COMPRESS_HW_SPEC_STEP_R0 4;;
let r1 = steady_leg SHA256_COMPRESS_HW_SPEC_STEP_R1 5;;
let r2 = steady_leg SHA256_COMPRESS_HW_SPEC_STEP_R2 6;;
let r3 = steady_leg SHA256_COMPRESS_HW_SPEC_STEP_R3 7;;

let (pH,qH,fH) = strip_atom head;;
let pHc = rebase pH and qHc = rebase qH;;
let pr0c = rebase (let (p,_,_)=strip_atom r0 in p);;
let pr1c = rebase (let (p,_,_)=strip_atom r1 in p);;
let pr2c = rebase (let (p,_,_)=strip_atom r2 in p);;
let pr3c = rebase (let (p,_,_)=strip_atom r3 in p);;
let qr3c = rebase (let (_,q,_)=strip_atom r3 in q);;

(* global riders (from head POST): YMM9/10 (init packs, consumed by FEEDFWD) +
   RDI=sptr (carried to final POST).  RSI is NOT carried (dropped after head). *)
let ymm9  = findc "YMM9_SSE" qHc;;
let ymm10 = findc "YMM10_SSE" qHc;;
let rdi   = findc "read RDI" qHc;;
let riders = [ymm9; ymm10; rdi];;

(* K-window carry terms @ 64/96/128 (kquad6/7/8), bound to sv, pulled by offset *)
let kq64  = kread_in "64"  pr1c;;   (* r1 reads @64  = kquad6 *)
let kq96  = kread_in "96"  pr2c;;   (* r2 reads @96  = kquad7 *)
let kq128 = kread_in "128" pr3c;;   (* r3 reads @128 = kquad8 *)
(* @32 = kquad5 for composed PRE (r0 reads it) *)
let kq32  = kread_in "32"  pr0c;;

let core cs = filter keepseam cs;;
(* composed PRE = head PRE + carried K window {32,64,96,128} *)
let pre_lam  = mk_abs(sv, list_mk_conj (pHc @ [kq32; kq64; kq96; kq128]));;
(* seams: next leg's PRE-core + riders + K quads strictly beyond what it reads *)
let seamR0 = mk_abs(sv, list_mk_conj (core pr0c @ riders @ [kq64; kq96; kq128]));;
let seamR1 = mk_abs(sv, list_mk_conj (core pr1c @ riders @ [kq96; kq128]));;
let seamR2 = mk_abs(sv, list_mk_conj (core pr2c @ riders @ [kq128]));;
let seamR3 = mk_abs(sv, list_mk_conj (core pr3c @ riders));;
(* composed POST = r3 POST + riders *)
let post_lam = mk_abs(sv, list_mk_conj (qr3c @ riders));;

let ens_head = rator(rator(rator(ens_of head)));;
let mk_ensures p q c = mk_comb(mk_comb(mk_comb(ens_head,p),q),c);;
let bvars = [`pc:num`;`kbase:num`;`kptr:int64`;`m:int32 list`;
             `q0:int128`;`q1:int128`;`mptr:int64`;`sptr:int64`];;
let comp_hyps = list_mk_conj
 [`aligned 16 (kptr:int64)`;
  `aligned 16 (word_add (kptr:int64) (word 384))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551488))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551520))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551552))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551584))`];;
let comp_concl = list_mk_forall(bvars, mk_imp(comp_hyps, mk_ensures pre_lam post_lam fH));;
Printf.printf "MONO_B concl built.\n%!";;

let SHA256_COMPRESS_HW_MONO_B = prove
 (comp_concl,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  SUBGOAL_THEN `aligned 16 (word_add (kptr:int64) (word 32))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORMALIZE_ALIGNED_WORD_CONV
       `aligned 16 (word_add (kptr:int64) (word 32))`]; ALL_TAC] THEN
  SUBGOAL_THEN `aligned 16 (word_add (kptr:int64) (word 64))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORMALIZE_ALIGNED_WORD_CONV
       `aligned 16 (word_add (kptr:int64) (word 64))`]; ALL_TAC] THEN
  SUBGOAL_THEN `aligned 16 (word_add (kptr:int64) (word 96))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORMALIZE_ALIGNED_WORD_CONV
       `aligned 16 (word_add (kptr:int64) (word 96))`]; ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `pc + 0xf4` seamR0 THEN CONJ_TAC THENL
   [MP_TAC(REWRITE_RULE[SOME_FLAGS] head) THEN ASM_REWRITE_TAC[] THEN
    ENSURES_SUBLEMMA_TAC execup "s" "s'" THEN ASM_REWRITE_TAC[];
    ENSURES_SEQUENCE_TAC `pc + 0x120` seamR1 THEN CONJ_TAC THENL
     [MP_TAC(REWRITE_RULE[SOME_FLAGS] r0) THEN ASM_REWRITE_TAC[] THEN
      ENSURES_SUBLEMMA_TAC execup "s" "s'" THEN ASM_REWRITE_TAC[];
      ENSURES_SEQUENCE_TAC `pc + 0x14d` seamR2 THEN CONJ_TAC THENL
       [MP_TAC(REWRITE_RULE[SOME_FLAGS] r1) THEN ASM_REWRITE_TAC[] THEN
        ENSURES_SUBLEMMA_TAC execup "s" "s'" THEN ASM_REWRITE_TAC[];
        ENSURES_SEQUENCE_TAC `pc + 0x17a` seamR3 THEN CONJ_TAC THENL
         [MP_TAC(REWRITE_RULE[SOME_FLAGS] r2) THEN ASM_REWRITE_TAC[] THEN
          ENSURES_SUBLEMMA_TAC execup "s" "s'" THEN ASM_REWRITE_TAC[];
          MP_TAC(REWRITE_RULE[SOME_FLAGS] r3) THEN ASM_REWRITE_TAC[] THEN
          ENSURES_SUBLEMMA_TAC execup "s" "s'" THEN ASM_REWRITE_TAC[]]]]]);;

Printf.printf "S049_MONO_B hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_MONO_B))
  (List.length(frees(concl SHA256_COMPRESS_HW_MONO_B)));;
Printf.printf "S049_MONO_B_DONE\n%!";;

(* ========================================================================= *)
(* Session 049 -- MONOLITH CHECKPOINT C: head ; R0..R3 ; G8..G12,             *)
(* pc+0x07 -> pc+0x297.  10 legs = head + a full 9-group steady run (g4..g12). *)
(* Uses a generic recursive nested-ENSURES_SEQUENCE composer driven by an       *)
(* ordered leg list; all 9 K window quads @32..@288 (kquad5..kquad13) ride the *)
(* read-only frame (composed PRE lists them all; each seam re-states the       *)
(* not-yet-consumed tail of the window + the YMM9/10/RDI riders).  hyps=0.       *)
(* ========================================================================= *)
(* S049 MONO_C: head ; R0[g4];R1[g5];R2[g6];R3[g7];G8;G9;G10;G11;G12,
   pc+0x07 -> pc+0x297.  10 legs = head + a full 9-group steady run (g4..g12).
   Uses a generic recursive nested-ENSURES_SEQUENCE composer, driven by an
   ordered leg list; all K window quads @32..@288 ride the read-only frame
   (composed PRE + every seam carries the not-yet-consumed tail of the window).
   riders = YMM9/YMM10 (init ABEF/CDGH packs, for FEEDFWD) + RDI=sptr. *)

let strip_atom th =
  let bod = snd(strip_forall(concl th)) in
  let ens = if is_imp bod then snd(dest_imp bod) else bod in
  let l,c = dest_comb ens in let l2,q = dest_comb l in
  let _,p = dest_comb l2 in (p,q,c);;
let ens_of th = let bod = snd(strip_forall(concl th)) in
  if is_imp bod then snd(dest_imp bod) else bod;;
let conjs_of_lam q = let s,body = dest_abs q in s, conjuncts body;;
let contains s sub =
  let ls=String.length s and lsub=String.length sub in
  let rec go i = i+lsub<=ls && (String.sub s i lsub = sub || go(i+1)) in go 0;;
let findc sub cs = find (fun c -> contains (string_of_term c) sub) cs;;
let is_kread off c =
  is_eq c && contains (string_of_term c) "bytes128"
          && contains (string_of_term c) ("(word " ^ off ^ ")");;
let kread_in off cs = find (is_kread off) cs;;
let nred_rule = CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV
                          THENC DEPTH_CONV NUM_SUB_CONV THENC DEPTH_CONV NUM_LE_CONV);;
let keepseam c = not(contains (string_of_term c) "bytes_loaded")
                 && not(contains (string_of_term c) "read RIP");;
let sv = `s:x86state`;;
let rebase lam = let s,cs = conjs_of_lam lam in map (vsubst[sv,s]) cs;;

let stlist = `[word_subword (q0:int128) (0,32); word_subword q0 (32,32);
               word_subword q0 (64,32); word_subword q0 (96,32);
               word_subword (q1:int128) (0,32); word_subword q1 (32,32);
               word_subword q1 (64,32); word_subword q1 (96,32)] : int32 list`;;
let kquad n =
  let el j = list_mk_comb(`EL:num->(int32)list->int32`,
               [mk_small_numeral(4*n+j);`sha256_constants:int32 list`]) in
  list_mk_comb(`WQUAD:int32->int32->int32->int32->int128`,[el 0;el 1;el 2;el 3]);;
let steady_leg th g =
  let sp = SPECL [`pc:num`;`kbase:num`;`kptr:int64`;`m:int32 list`;stlist;
                  mk_small_numeral g] th in
  REWRITE_RULE[] (nred_rule (SPEC (kquad (g+1)) sp));;

let head = INST [kquad 4, `kq4:int128`] (SPEC_ALL SHA256_COMPRESS_HW_CORE_HEAD_ABS);;
(* ordered steady legs (leg thm, group index, entry-pc, exit-pc) *)
let steadies =
 [ (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_R0  4),  4, 0x0f4, 0x120;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_R1  5),  5, 0x120, 0x14d;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_R2  6),  6, 0x14d, 0x17a;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_R3  7),  7, 0x17a, 0x1a7;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_G8  8),  8, 0x1a7, 0x1d7;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_G9  9),  9, 0x1d7, 0x207;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_G10 10), 10, 0x207, 0x237;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_G11 11), 11, 0x237, 0x267;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_G12 12), 12, 0x267, 0x297 ];;

let (pH,qH,fH) = strip_atom head;;
let pHc = rebase pH and qHc = rebase qH;;
(* riders from head POST *)
let ymm9  = findc "YMM9_SSE" qHc;;
let ymm10 = findc "YMM10_SSE" qHc;;
let rdi   = findc "read RDI" qHc;;
let riders = [ymm9; ymm10; rdi];;

(* harvest the K-window term for each offset 32,64,...,288 (kquad5..13). Each
   offset @(32k) appears as the "next" read of the leg for group (3+k). Grab it
   from that leg's rebased PRE. *)
let leg_pre th = rebase (let (p,_,_)=strip_atom th in p);;
let leg_th (th,_,_,_) = th;;
let winoffs = [32;64;96;128;160;192;224;256;288];;   (* kquad5..kquad13 *)
(* offset @(32k): "next" read of steadies.(k-1) (0-indexed). *)
let kwin =
  map (fun off ->
    let k = off/32 in
    let leg = el (k-1) steadies in
    off, kread_in (string_of_int off) (leg_pre (leg_th leg))) winoffs;;
let kterm off = assoc off kwin;;

let core cs = filter keepseam cs;;
(* seam predicate at the entry-pc of a steady leg reading @c,@c+32:
   leg PRE-core + riders + {kquad @ o : o > c+32, o in winoffs} *)
let seam_for (th,g,_,_) =
  let c = 32*(g-4) in
  let carry = map kterm (filter (fun w -> not(w <= c+32)) winoffs) in
  mk_abs(sv, list_mk_conj (core (leg_pre th) @ riders @ carry));;

(* composed PRE = head PRE-core + all K window quads (ride through head) *)
let pre_lam = mk_abs(sv, list_mk_conj (pHc @ List.map kterm winoffs));;
(* composed POST = g12 POST + riders *)
let g12th = leg_th (List.nth steadies 8);;
let qg12c = rebase (let (_,q,_)=strip_atom g12th in q);;
let post_lam = mk_abs(sv, list_mk_conj (qg12c @ riders));;

let ens_head = rator(rator(rator(ens_of head)));;
let mk_ensures p q c = mk_comb(mk_comb(mk_comb(ens_head,p),q),c);;
let bvars = [`pc:num`;`kbase:num`;`kptr:int64`;`m:int32 list`;
             `q0:int128`;`q1:int128`;`mptr:int64`;`sptr:int64`];;
let comp_hyps = list_mk_conj
 [`aligned 16 (kptr:int64)`;
  `aligned 16 (word_add (kptr:int64) (word 384))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551488))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551520))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551552))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551584))`];;
let comp_concl = list_mk_forall(bvars, mk_imp(comp_hyps, mk_ensures pre_lam post_lam fH));;
Printf.printf "MONO_C concl built.\n%!";;

(* leg tactic: MP the leg (SOME_FLAGS expanded), stock ENSURES_SUBLEMMA. *)
let leg_tac th =
  MP_TAC(REWRITE_RULE[SOME_FLAGS] th) THEN ASM_REWRITE_TAC[] THEN
  ENSURES_SUBLEMMA_TAC execup "s" "s'" THEN ASM_REWRITE_TAC[];;
let pcterm n = mk_comb(mk_comb(`(+):num->num->num`,`pc:num`), mk_small_numeral n);;
(* the nested composer: entries = (seam_off, seam_Q, disch_leg) for each internal
   seam; the final leg closes to composed POST. *)
let rec build entries final = match entries with
  | [] -> leg_tac final
  | (off,seam,disch)::rest ->
      ENSURES_SEQUENCE_TAC (pcterm off) seam THEN
      CONJ_TAC THENL [ leg_tac disch; build rest final ];;

(* entries: at each steady leg's ENTRY pc, seam = that leg's PRE, discharged by
   the PREVIOUS leg (head for R0).  The last steady (g12) is the FINAL leg, so
   the last entry is (0x267, g12.pre, g11) and g12 closes the innermost.  9
   entries (R0..G12 entries), final=g12: 10 legs total (head + 9 steadies). *)
let entries =
  let rec go prev = function
    | [] -> []
    | (th,g,e,x)::rest -> (e, seam_for (th,g,e,x), prev) :: go th rest in
  match steadies with
  | (th0,g0,e0,x0)::rest -> (e0, seam_for (th0,g0,e0,x0), head) :: go th0 rest
  | [] -> failwith "no steadies";;
Printf.printf "entries=%d (expect 9)\n%!" (List.length entries);;

let SHA256_COMPRESS_HW_MONO_C = prove
 (comp_concl,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  SUBGOAL_THEN `aligned 16 (word_add (kptr:int64) (word 32))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORMALIZE_ALIGNED_WORD_CONV
       `aligned 16 (word_add (kptr:int64) (word 32))`]; ALL_TAC] THEN
  SUBGOAL_THEN `aligned 16 (word_add (kptr:int64) (word 64))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORMALIZE_ALIGNED_WORD_CONV
       `aligned 16 (word_add (kptr:int64) (word 64))`]; ALL_TAC] THEN
  SUBGOAL_THEN `aligned 16 (word_add (kptr:int64) (word 96))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORMALIZE_ALIGNED_WORD_CONV
       `aligned 16 (word_add (kptr:int64) (word 96))`]; ALL_TAC] THEN
  SUBGOAL_THEN `aligned 16 (word_add (kptr:int64) (word 128))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORMALIZE_ALIGNED_WORD_CONV
       `aligned 16 (word_add (kptr:int64) (word 128))`]; ALL_TAC] THEN
  SUBGOAL_THEN `aligned 16 (word_add (kptr:int64) (word 160))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORMALIZE_ALIGNED_WORD_CONV
       `aligned 16 (word_add (kptr:int64) (word 160))`]; ALL_TAC] THEN
  SUBGOAL_THEN `aligned 16 (word_add (kptr:int64) (word 192))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORMALIZE_ALIGNED_WORD_CONV
       `aligned 16 (word_add (kptr:int64) (word 192))`]; ALL_TAC] THEN
  SUBGOAL_THEN `aligned 16 (word_add (kptr:int64) (word 224))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORMALIZE_ALIGNED_WORD_CONV
       `aligned 16 (word_add (kptr:int64) (word 224))`]; ALL_TAC] THEN
  SUBGOAL_THEN `aligned 16 (word_add (kptr:int64) (word 256))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORMALIZE_ALIGNED_WORD_CONV
       `aligned 16 (word_add (kptr:int64) (word 256))`]; ALL_TAC] THEN
  build entries g12th);;

Printf.printf "S049_MONO_C hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_MONO_C))
  (List.length(frees(concl SHA256_COMPRESS_HW_MONO_C)));;
Printf.printf "S049_MONO_C_DONE\n%!";;

(* ========================================================================= *)
(* Session 049 -- THE FULL MONOLITH (CORE_ABS): head ; R0..R3 ; G8..G12 ;     *)
(* CORE_TAIL3 ; FEEDFWD, pc+0x07 -> pc+0x30c.  12 legs.  The complete          *)
(* register-only 64-round SHA-NI core + feed-forward, threading ONLY opaque    *)
(* compress_rounds/WWIN accumulators (the s030 mandate; resolves the s043       *)
(* exponential-concrete-threading blocker).  Extends the MONO_C composer with   *)
(* the tail leg (CORE_TAIL3 inst: l:=cr m st 52, kq0:=kquad13, a3..a6 =         *)
(* WWIN48/WWIN52/PADP40/MSG1P44; kqA@320/kqB@352 ride the read-only frame) and  *)
(* the register-only FEEDFWD leg (init ABEF/CDGH from YMM9/10 riders).  Frame = *)
(* head frame (+) RDX (tail's dec-rdx) -- a strict superset of every leg.       *)
(* reflexive feedfwd seam -> ENSURES_SUBLEMMA_REFL_TAC fallback.  hyps=0.        *)
(* POST carries the tail's concrete cr 52->64 CR4-nesting + feed-forward add;    *)
(* folding it back to compress_rounds m st 64 + sha256_block is the next         *)
(* milestone (spec connection).                                                *)
(* ========================================================================= *)
(* S049 CORE_ABS: THE FULL MONOLITH.  head ; R0..R3 ; G8..G12 ; CORE_TAIL3 ;
   FEEDFWD, pc+0x07 -> pc+0x30c.  12 legs.  Extends the MONO_C composer with the
   tail (non-reflexive: kqA@320/kqB@352 ride the frame) + feedfwd (register-only).
   POST @ pc+0x30c: YMM1 = ABEF feed-forward, YMM2 = CDGH feed-forward, i.e. the
   opaque compress_rounds m st 64 crypto state added to the initial state.
   ONE prove, nested ENSURES_SEQUENCE, all legs leaf atoms. *)

let strip_atom th =
  let bod = snd(strip_forall(concl th)) in
  let ens = if is_imp bod then snd(dest_imp bod) else bod in
  let l,c = dest_comb ens in let l2,q = dest_comb l in
  let _,p = dest_comb l2 in (p,q,c);;
let ens_of th = let bod = snd(strip_forall(concl th)) in
  if is_imp bod then snd(dest_imp bod) else bod;;
let conjs_of_lam q = let s,body = dest_abs q in s, conjuncts body;;
let contains s sub =
  let ls=String.length s and lsub=String.length sub in
  let rec go i = i+lsub<=ls && (String.sub s i lsub = sub || go(i+1)) in go 0;;
let findc sub cs = find (fun c -> contains (string_of_term c) sub) cs;;
let is_kread off c =
  is_eq c && contains (string_of_term c) "bytes128"
          && contains (string_of_term c) ("(word " ^ off ^ ")");;
let kread_in off cs = find (is_kread off) cs;;
let nred_rule = CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV
                          THENC DEPTH_CONV NUM_SUB_CONV THENC DEPTH_CONV NUM_LE_CONV);;
let keepseam c = not(contains (string_of_term c) "bytes_loaded")
                 && not(contains (string_of_term c) "read RIP");;
let sv = `s:x86state`;;
let rebase lam = let s,cs = conjs_of_lam lam in map (vsubst[sv,s]) cs;;

let stlist = `[word_subword (q0:int128) (0,32); word_subword q0 (32,32);
               word_subword q0 (64,32); word_subword q0 (96,32);
               word_subword (q1:int128) (0,32); word_subword q1 (32,32);
               word_subword q1 (64,32); word_subword q1 (96,32)] : int32 list`;;
let kquad n =
  let el j = list_mk_comb(`EL:num->(int32)list->int32`,
               [mk_small_numeral(4*n+j);`sha256_constants:int32 list`]) in
  list_mk_comb(`WQUAD:int32->int32->int32->int32->int128`,[el 0;el 1;el 2;el 3]);;
let steady_leg th g =
  let sp = SPECL [`pc:num`;`kbase:num`;`kptr:int64`;`m:int32 list`;stlist;
                  mk_small_numeral g] th in
  REWRITE_RULE[] (nred_rule (SPEC (kquad (g+1)) sp));;

let head = INST [kquad 4, `kq4:int128`] (SPEC_ALL SHA256_COMPRESS_HW_CORE_HEAD_ABS);;
let steadies =
 [ (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_R0  4),  4, 0x0f4, 0x120;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_R1  5),  5, 0x120, 0x14d;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_R2  6),  6, 0x14d, 0x17a;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_R3  7),  7, 0x17a, 0x1a7;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_G8  8),  8, 0x1a7, 0x1d7;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_G9  9),  9, 0x1d7, 0x207;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_G10 10), 10, 0x207, 0x237;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_G11 11), 11, 0x237, 0x267;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_G12 12), 12, 0x267, 0x297 ];;

(* ---- the tail leg: CORE_TAIL3 instantiated at the g12->tail boundary ---- *)
(* l := cr m st 52 ; kq0 := kquad13 (=G12's @288 POST) ; a3..a6 = ring shapes *)
let stlist_cr52 = `sha256_compress_rounds m
    [word_subword (q0:int128) (0,32); word_subword q0 (32,32);
     word_subword q0 (64,32); word_subword q0 (96,32);
     word_subword (q1:int128) (0,32); word_subword q1 (32,32);
     word_subword q1 (64,32); word_subword q1 (96,32)] 52 : int32 list`;;
let tail = SPECL [`pc:num`;`kbase:num`;`kptr:int64`; stlist_cr52;
                  kquad 13; `kqA:int128`; `kqB:int128`;
                  `WWIN m 48:int128`;`WWIN m 52:int128`;
                  `PADP m 40:int128`;`MSG1P m 44:int128`]
             SHA256_COMPRESS_HW_CORE_TAIL3;;

let (pH,qH,fH) = strip_atom head;;
let pHc = rebase pH and qHc = rebase qH;;
let ymm9  = findc "YMM9_SSE" qHc;;
let ymm10 = findc "YMM10_SSE" qHc;;
let rdi   = findc "read RDI" qHc;;
let riders = [ymm9; ymm10; rdi];;

let leg_pre th = rebase (let (p,_,_)=strip_atom th in p);;
let leg_th (th,_,_,_) = th;;
(* the K window: steady offsets 32..288 + tail-only 320,352 *)
let steady_offs = [32;64;96;128;160;192;224;256;288];;   (* kquad5..kquad13 *)
let tail_offs   = [320;352];;                            (* kqA, kqB *)
let allwin = steady_offs @ tail_offs;;
(* per steady offset @(32k): "next" read of steadies.(k-1). *)
let steady_kterm off =
  let k = off/32 in let leg = List.nth steadies (k-1) in
  kread_in (string_of_int off) (leg_pre (leg_th leg));;
(* tail K reads: pull kqA@320, kqB@352 straight from tail PRE. *)
let pTc = rebase (let (p,_,_)=strip_atom tail in p);;
let kterm off =
  if off <= 288 then steady_kterm off else kread_in (string_of_int off) pTc;;

let core cs = filter keepseam cs;;
(* steady seam @entry of leg g reading @c,@c+32: leg PRE + riders + window tail *)
let seam_steady (th,g,_,_) =
  let c = 32*(g-4) in
  let carry = map kterm (filter (fun w -> not(w <= c+32)) allwin) in
  mk_abs(sv, list_mk_conj (core (leg_pre th) @ riders @ carry));;
(* tail seam @0x297: tail PRE (reads @288,@320,@352) + riders.  No K beyond @352
   so no extra carry; but riders still ride (feedfwd needs YMM9/10). *)
let seam_tail =
  mk_abs(sv, list_mk_conj (core pTc @ riders));;
(* feedfwd seam @0x302: feedfwd PRE = YMM1(abef=tail.YMM1), YMM2(cdgh=tail.YMM2),
   YMM9(initabef), YMM10(initcdgh).  Built from tail POST + riders. *)
let (_,qTail,_) = strip_atom tail;;
let qTailc = rebase qTail;;
let ff_abef = findc "YMM1_SSE" qTailc;;   (* abef = tail POST YMM1 *)
let ff_cdgh = findc "YMM2_SSE" qTailc;;   (* cdgh = tail POST YMM2 *)
let seam_ff = mk_abs(sv, list_mk_conj [ff_abef; ff_cdgh; ymm9; ymm10]);;

(* feedfwd leg, instantiated: abef/cdgh from tail POST, initabef/initcdgh from riders *)
let abef_rhs = snd(dest_eq ff_abef) and cdgh_rhs = snd(dest_eq ff_cdgh);;
let initabef_rhs = snd(dest_eq ymm9) and initcdgh_rhs = snd(dest_eq ymm10);;
let feedfwd = SPECL [`pc:num`;`kbase:num`; abef_rhs; cdgh_rhs; initabef_rhs; initcdgh_rhs]
               SHA256_COMPRESS_HW_FEEDFWD;;
let (_,qFF,_) = strip_atom feedfwd;;
let post_lam = qFF;;   (* final POST = feedfwd POST (already stated over the terms) *)

(* composed PRE = head PRE-core + full K window (steady + tail) *)
let pre_lam = mk_abs(sv, list_mk_conj (pHc @ map kterm allwin));;

let ens_head = rator(rator(rator(ens_of head)));;
let mk_ensures p q c = mk_comb(mk_comb(mk_comb(ens_head,p),q),c);;
(* composed frame = head frame (RIP;RSI + YMM0..10 + flags + events) PLUS RDX
   (the tail's dec-rdx frame MAYCHANGE [RDX] is not in the head frame). This is
   a strict SUPERSET of every leg frame -> SUBSUMED_MAYCHANGE closes each leg. *)
let comp_frame =
  `MAYCHANGE [RIP; RSI; RDX] ,,
   MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM5_SSE;
              YMM6_SSE; YMM7_SSE; YMM8_SSE; YMM9_SSE; YMM10_SSE] ,,
   MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;
let bvars = [`pc:num`;`kbase:num`;`kptr:int64`;`m:int32 list`;
             `q0:int128`;`q1:int128`;`mptr:int64`;`sptr:int64`;`kqA:int128`;`kqB:int128`];;
let comp_hyps = list_mk_conj
 [`aligned 16 (kptr:int64)`;
  `aligned 16 (word_add (kptr:int64) (word 384))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551488))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551520))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551552))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551584))`];;
let comp_concl = list_mk_forall(bvars, mk_imp(comp_hyps, mk_ensures pre_lam post_lam comp_frame));;
Printf.printf "CORE_ABS concl built. frees(concl)=%d\n%!" (List.length(frees comp_concl));;

let pcterm n = mk_comb(mk_comb(`(+):num->num->num`,`pc:num`), mk_small_numeral n);;
(* stock sublemma for non-reflexive seams, REFL variant for the perfectly-
   reflexive ones (feedfwd's seam == its instantiated PRE -> P=>P' collapses to
   T -> stock dest_binder failure).  Try stock first, fall back to REFL. *)
let leg_tac th =
  MP_TAC(REWRITE_RULE[SOME_FLAGS] th) THEN ASM_REWRITE_TAC[] THEN
  (ENSURES_SUBLEMMA_TAC execup "s" "s'" ORELSE
   ENSURES_SUBLEMMA_REFL_TAC execup "s" "s'") THEN ASM_REWRITE_TAC[];;
let rec build entries final = match entries with
  | [] -> leg_tac final
  | (off,seam,disch)::rest ->
      ENSURES_SEQUENCE_TAC (pcterm off) seam THEN
      CONJ_TAC THENL [ leg_tac disch; build rest final ];;

(* entries: 9 steady-entry seams (R0..G12, disch by prev leg) + tail-entry seam
   @0x297 (disch by G12) + feedfwd-entry seam @0x302 (disch by tail); final=feedfwd. *)
let steady_entries =
  let rec go prev = function
    | [] -> []
    | (th,g,e,x)::rest -> (e, seam_steady (th,g,e,x), prev) :: go th rest in
  match steadies with
  | (th0,g0,e0,x0)::rest -> (e0, seam_steady (th0,g0,e0,x0), head) :: go th0 rest
  | [] -> failwith "no steadies";;
let g12th = leg_th (List.nth steadies 8);;
let entries = steady_entries @
  [ 0x297, seam_tail, g12th;     (* tail-entry seam, discharged by G12 *)
    0x302, seam_ff,   tail ];;   (* feedfwd-entry seam, discharged by tail *)
Printf.printf "entries=%d (expect 11)\n%!" (List.length entries);;

let mk_align_term n =
  vsubst [mk_small_numeral n, `n:num`]
    `aligned 16 (word_add (kptr:int64) (word n))`;;
let mk_align_sub n =
  let t = mk_align_term n in
  SUBGOAL_THEN t ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORMALIZE_ALIGNED_WORD_CONV t]; ALL_TAC];;

let SHA256_COMPRESS_HW_CORE_ABS = prove
 (comp_concl,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  EVERY (map mk_align_sub [32;64;96;128;160;192;224;256;288;320;352]) THEN
  build entries feedfwd);;

Printf.printf "S049_CORE_ABS hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_CORE_ABS))
  (List.length(frees(concl SHA256_COMPRESS_HW_CORE_ABS)));;
Printf.printf "S049_CORE_ABS_DONE\n%!";;

(* ========================================================================= *)
(* Session 050 -- CORE_ABS_SPEC: the SPEC CONNECTION.                         *)
(*                                                                           *)
(* CORE_ABS's POST carries the tail drain in CONCRETE crypto vocabulary: its  *)
(* YMM1/YMM2 = simd4 word_add (ABEF/CDGH_PACK of X) (ABEF/CDGH_PACK of init),  *)
(* where X = CR4 (CR4 (CR4 (cr m st 52) wk52) wk56) wk60 is the last three     *)
(* groups drained into the accumulator with two FREE K binders kqA@+320,       *)
(* kqB@+352.  CORE_ABS_SPEC restates that POST in pure spec form               *)
(*   YMM1 = ABEF_PACK (EL 0 blk)(EL 1 blk)(EL 4 blk)(EL 5 blk)                 *)
(*   YMM2 = CDGH_PACK (EL 2 blk)(EL 3 blk)(EL 6 blk)(EL 7 blk)                 *)
(* where blk = sha256_block m st and st = the ABEF/CDGH-loaded init state      *)
(* [q0 lanes; q1 lanes].  This is EXACTLY the state the exit repack + store    *)
(* consumes, and connects the 64-round core to the FIPS 180-4 block function.  *)
(*                                                                           *)
(* Method (nohw SHA256_BLOCK_NOHW_HEAD16_ABS pattern -- INST + REWRITE by      *)
(* proven folds, soundness-preserving by construction; a wrong K->EL mapping   *)
(* would make a fold fail, not silently pass):                                 *)
(*  (0) INST the two free K binders to the constants the K reads @+320/+352     *)
(*      actually equal: kqA := WQUAD(EL 56..59 sha256_constants),              *)
(*      kqB := WQUAD(EL 60..63).  (Verified: g13 consumes @+288 = EL52..55,    *)
(*      so @+320 = EL56..59 and @+352 = EL60..63 by the +32 = +8 dwords step.) *)
(*  (A) fold X -> sha256_compress_rounds m st 64 via CR4_SPEC_STEP_WWIN        *)
(*      (g=13,14,15) + the schedule-ring folds WRING_WWIN(40)/PADP(44)/        *)
(*      WRING_WWIN(44) -- the same folds the steady SPEC_STEP legs use.  NOTE   *)
(*      the schedule-window offsets are reduced with ADD-only (8*4 in the       *)
(*      palignr must survive to match PADP's definition), the CR4 crypto steps  *)
(*      with MULT+ADD.                                                          *)
(*  (B) distribute the feed-forward simd4 word_add over the ABEF/CDGH packs     *)
(*      (SIMD4_ADD_ABEF/CDGH: a pack is a reversed WQUAD, so the lane-wise      *)
(*      SIMD4_ADD_WQUAD_SUBWORD applies), giving ABEF/CDGH_PACK of word_add of  *)
(*      the cr64 lanes and the init-state lanes.                                *)
(*  (C) fold word_add (EL i (cr m st 64)) (EL i st) -> EL i (sha256_block m st) *)
(*      via GSYM BLOCK_ELS (sha256_block unfolded + EL_CONV to concrete lanes). *)
(* ========================================================================= *)

(* A packed ABEF/CDGH register is a WQUAD of its four dwords in reverse order   *)
(* (word_join is big-endian: the last argument occupies the low dword).         *)
let ABEF_AS_WQUAD = prove
 (`!a b e f:int32. ABEF_PACK a b e f = WQUAD f e b a`,
  REWRITE_TAC[ABEF_PACK; WQUAD]);;
let CDGH_AS_WQUAD = prove
 (`!c d g h:int32. CDGH_PACK c d g h = WQUAD h g d c`,
  REWRITE_TAC[CDGH_PACK; WQUAD]);;

(* Feed-forward lane distribution: simd4 word_add of two packs is the pack of   *)
(* the lane-wise word_adds (the sha256_block feed-forward, in the packed domain).*)
let SIMD4_ADD_ABEF = prove
 (`!a b e f a' b' e' f':int32.
     simd4 word_add (ABEF_PACK a b e f) (ABEF_PACK a' b' e' f') =
     ABEF_PACK (word_add a a') (word_add b b') (word_add e e') (word_add f f')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ABEF_AS_WQUAD] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM WQUAD_EXPAND] THEN
  REWRITE_TAC[SIMD4_ADD_WQUAD_SUBWORD]);;
let SIMD4_ADD_CDGH = prove
 (`!c d g h c' d' g' h':int32.
     simd4 word_add (CDGH_PACK c d g h) (CDGH_PACK c' d' g' h') =
     CDGH_PACK (word_add c c') (word_add d d') (word_add g g') (word_add h h')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CDGH_AS_WQUAD] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM WQUAD_EXPAND] THEN
  REWRITE_TAC[SIMD4_ADD_WQUAD_SUBWORD]);;

(* EL i (sha256_block m st) = word_add (EL i (cr m st 64)) (EL i st), with the   *)
(* RHS's `EL i st` reduced to its concrete q0/q1 lane (matching the POST's       *)
(* init-state lanes, which arrive concrete from the YMM9/YMM10 feed-fwd riders). *)
let SHA256_COMPRESS_HW_BLOCK_ELS =
  let stl = `[word_subword (q0:int128) (0,32); word_subword q0 (32,32);
              word_subword q0 (64,32); word_subword q0 (96,32);
              word_subword (q1:int128) (0,32); word_subword q1 (32,32);
              word_subword q1 (64,32); word_subword q1 (96,32)] : int32 list` in
  CONV_RULE(DEPTH_CONV EL_CONV) (prove
   (list_mk_conj (map (fun i ->
       let eli l = list_mk_comb(`EL:num->(int32)list->int32`,[mk_small_numeral i; l]) in
       mk_eq(eli (list_mk_comb(`sha256_block`,[`m:int32 list`; stl])),
             list_mk_comb(`word_add:int32->int32->int32`,
               [eli (list_mk_comb(`sha256_compress_rounds`,[`m:int32 list`;stl;`64`]));
                eli stl])))
       [0;1;2;3;4;5;6;7]),
    REWRITE_TAC[sha256_block] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]));;

let SHA256_COMPRESS_HW_CORE_ABS_SPEC =
  let stl = `[word_subword (q0:int128) (0,32); word_subword q0 (32,32);
              word_subword q0 (64,32); word_subword q0 (96,32);
              word_subword (q1:int128) (0,32); word_subword q1 (32,32);
              word_subword q1 (64,32); word_subword q1 (96,32)] : int32 list` in
  let kqA_val = `WQUAD (EL 56 sha256_constants) (EL 57 sha256_constants)
                       (EL 58 sha256_constants) (EL 59 sha256_constants) : int128` in
  let kqB_val = `WQUAD (EL 60 sha256_constants) (EL 61 sha256_constants)
                       (EL 62 sha256_constants) (EL 63 sha256_constants) : int128` in
  let core_abs' = INST [kqA_val, `kqA:int128`; kqB_val, `kqB:int128`]
                    (SPEC_ALL SHA256_COMPRESS_HW_CORE_ABS) in
  let nred_cr  = CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV) in
  let nred_off = CONV_RULE(DEPTH_CONV NUM_ADD_CONV) in
  let cr_step g = nred_cr (SPECL [`m:int32 list`; stl; mk_small_numeral g]
                            CR4_SPEC_STEP_WWIN) in
  let cr52 = cr_step 13 and cr56 = cr_step 14 and cr60 = cr_step 15 in
  let wring40 = nred_off (SPECL [`m:int32 list`; `40`] WRING_WWIN) in
  let wring44 = nred_off (SPECL [`m:int32 list`; `44`] WRING_WWIN) in
  let padp44  = GSYM(nred_off (SPECL [`m:int32 list`; `44`] PADP)) in
  let step1 = REWRITE_RULE[wring40; padp44; wring44; cr52; cr56; cr60] core_abs' in
  let step2 = REWRITE_RULE[SIMD4_ADD_ABEF; SIMD4_ADD_CDGH] step1 in
  let step3 = REWRITE_RULE[GSYM SHA256_COMPRESS_HW_BLOCK_ELS] step2 in
  GEN_ALL step3;;

Printf.printf "S050_CORE_ABS_SPEC hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_CORE_ABS_SPEC))
  (List.length(frees(concl SHA256_COMPRESS_HW_CORE_ABS_SPEC)));;
Printf.printf "S050_CORE_ABS_SPEC_DONE\n%!";;

(* ========================================================================= *)
(* Phase 5 -- EXIT: repack ABEF/CDGH back to natural state order + movdqu       *)
(* store.  The mirror image of ENTRY_REPACK (above): after the 64-round core    *)
(* + feed-forward (CORE_ABS_SPEC), YMM1 = ABEF_PACK a b e f and YMM2 =          *)
(* CDGH_PACK c d g h hold the block output in the SHA-NI register view; the      *)
(* epilogue (tmc pc+0x312 .. pc+0x334, ending at ret) repacks them into natural  *)
(* state order and stores the 8 words to [rdi]/[rdi+0x10]:                       *)
(*   pshufd $0xb1,xmm2,xmm2 ; pshufd $0x1b,xmm1,xmm7 ; pshufd $0xb1,xmm1,xmm1 ;   *)
(*   punpckhqdq xmm2,xmm1 ; palignr $0x8,xmm7,xmm2 ;                             *)
(*   movdqu xmm1,(rdi) ; movdqu xmm2,0x10(rdi).                                  *)
(* Net effect (verified by symbolic stepping + WORD_BLAST, the ENTRY_REPACK      *)
(* closer): [rdi] = WQUAD (abef lanes 3,2)(cdgh lanes 3,2) = {A,B,C,D},          *)
(* [rdi+0x10] = WQUAD (abef lanes 1,0)(cdgh lanes 1,0) = {E,F,G,H}, i.e. the     *)
(* natural-order 8-word state (word_join is big-endian, so lane 3 = word_subword *)
(* (96,32) is the low stored dword).  The store needs                           *)
(* `nonoverlapping (word pc, 825) (sptr, 32)` (825 = .text length) for the       *)
(* stepper's "will not modify program code" check -- ENTRY_REPACK does not since *)
(* it only reads.  Composed with CORE_ABS_SPEC at pc+0x312, this gives the       *)
(* single-block core body pc+0x07 -> pc+0x334 writing sha256_block to [rdi].     *)
(* ========================================================================= *)
let SHA256_COMPRESS_HW_EXIT = prove
 (`!pc kbase (sptr:int64) (abef:int128) (cdgh:int128).
     nonoverlapping (word pc, 825) (sptr, 32)
     ==> ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x312) /\
            read RDI s = sptr /\
            word_subword (read YMM1_SSE s) (0,128) = (abef:int128) /\
            word_subword (read YMM2_SSE s) (0,128) = (cdgh:int128))
       (\s. read RIP s = word (pc + 0x334) /\
            read RDI s = sptr /\
            read (memory :> bytes128 sptr) s =
              WQUAD (word_subword abef (96,32)) (word_subword abef (64,32))
                    (word_subword cdgh (96,32)) (word_subword cdgh (64,32)) /\
            read (memory :> bytes128 (word_add sptr (word 16))) s =
              WQUAD (word_subword abef (32,32)) (word_subword abef (0,32))
                    (word_subword cdgh (32,32)) (word_subword cdgh (0,32)))
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM1_SSE; YMM2_SSE; YMM7_SSE] ,,
        MAYCHANGE [memory :> bytes128 sptr;
                   memory :> bytes128 (word_add sptr (word 16))] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s5" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s6" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s7" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WQUAD] THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REPEAT CONJ_TAC THEN TRY REFL_TAC THEN CONV_TAC WORD_BLAST);;

Printf.printf "S050_EXIT hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_EXIT))
  (List.length(frees(concl SHA256_COMPRESS_HW_EXIT)));;
Printf.printf "S050_EXIT_DONE\n%!";;

(* ========================================================================= *)
(* Session 051 -- back-edge control-flow primitives (toward the single-block   *)
(* body pc+0x07 -> pc+0x334 and, ultimately, the Phase-6 multi-block loop).    *)
(*                                                                             *)
(* The core ends at the loop back-edge `jne 3c` at tmc pc+0x30c (obj 0x310).   *)
(* It reads ZF, which is set by the ONLY flag-setting instruction in the whole *)
(* core, `dec %rdx` at tmc pc+0x2fa (obj 0x2fe), buried inside the g15 tail     *)
(* group.  Every other core instruction (SHA256RNDS2/MSG1/MSG2, PADDD, PSHUFD, *)
(* PALIGNR, PUNPCK*, MOVDQU/A, PSHUFB) is flag-neutral, so ZF is preserved from *)
(* the dec all the way to the jne.  RDX itself is untouched from pc+0x07 to the *)
(* dec (verified: objdump shows no other %rdx write), so on entry to the dec    *)
(* RDX still holds num_blocks.  For a single block num_blocks=1 => RDX=1 =>      *)
(* dec sets RDX=0 => ZF=1 => the jne FALLS THROUGH to the epilogue at pc+0x312. *)
(*                                                                             *)
(* Two register-only primitives, both reused verbatim by Phase 6:              *)
(*  - JNE_FALLTHRU: given ZF set at pc+0x30c, step the single jne to pc+0x312.  *)
(*  - GROUP_STEP4_G15_RAW_PLUS: the g15 tail group (pc+0x2f0->0x302) with the    *)
(*    loop counter RDX threaded and the resulting ZF exposed in the POST (the    *)
(*    exact word-arithmetic shape the stepper emits for `dec %rdx`).  This is    *)
(*    G15_RAW strengthened; the crypto POST is byte-identical.                   *)
(* ========================================================================= *)

let SHA256_COMPRESS_HW_JNE_FALLTHRU = prove
 (`!pc kbase.
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x30c) /\
            read ZF s)
       (\s. read RIP s = word (pc + 0x312))
       (MAYCHANGE [RIP] ,, MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

Printf.printf "S051_JNE_BRIDGE hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_JNE_FALLTHRU))
  (List.length(frees(concl SHA256_COMPRESS_HW_JNE_FALLTHRU)));;
Printf.printf "S051_JNE_BRIDGE_DONE\n%!";;

let SHA256_COMPRESS_HW_GROUP_STEP4_G15_RAW_PLUS = prove
 (`!pc kbase (kptr:int64) mloc (mval:int128) wk abef cdgh
     (a3:int128) (a4:int128) (a5:int128) (a6:int128) (rdxin:int64).
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x2f0) /\
            read RCX s = kptr /\
            read RDX s = rdxin /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) = (abef:int128) /\
            word_subword (read YMM2_SSE s) (0,128) = (cdgh:int128) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (\s. read RIP s = word (pc + 0x302) /\
            read RCX s = kptr /\
            read RDX s = word_sub rdxin (word 1) /\
            (read ZF s <=> val (word_sub rdxin (word 1):int64) = 0) /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM2_SSE s) (0,128) = sha256_rnds2 cdgh abef wk /\
            word_subword (read YMM1_SSE s) (0,128) =
              sha256_rnds2 abef (sha256_rnds2 cdgh abef wk)
                           (word_subword wk (64,64) : int128) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE] ,, MAYCHANGE [RDX] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s5" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s6" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC SHA256_RNDS2_WK_CONG THEN CONJ_TAC THEN
      CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC) THEN
  TRY REFL_TAC);;

Printf.printf "S051_G15ZF hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_GROUP_STEP4_G15_RAW_PLUS))
  (List.length(frees(concl SHA256_COMPRESS_HW_GROUP_STEP4_G15_RAW_PLUS)));;
Printf.printf "S051_G15ZF_DONE\n%!";;

(* FEEDFWD_PLUS: the feed-forward paddd pair (pc+0x302 -> pc+0x30c) carrying ZF  *)
(* and RDX through unchanged.  The two SSE `paddd` do not touch EFLAGS, so ZF     *)
(* (set by the earlier `dec %rdx`) survives to the jne -- we expose that here and *)
(* tighten the frame to DROP SOME_FLAGS (the original FEEDFWD's SOME_FLAGS was a  *)
(* faithful over-approx).  RDX rides through too, keeping the loop counter live.  *)
let SHA256_COMPRESS_HW_FEEDFWD_PLUS = prove
 (`!pc kbase (abef:int128) (cdgh:int128) (initabef:int128) (initcdgh:int128)
     (rdxv:int64) zf.
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x302) /\
            read RDX s = rdxv /\
            read ZF s = zf /\
            word_subword (read YMM1_SSE s) (0,128) = (abef:int128) /\
            word_subword (read YMM2_SSE s) (0,128) = (cdgh:int128) /\
            word_subword (read YMM9_SSE s) (0,128) = (initabef:int128) /\
            word_subword (read YMM10_SSE s) (0,128) = (initcdgh:int128))
       (\s. read RIP s = word (pc + 0x30c) /\
            read RDX s = rdxv /\
            read ZF s = zf /\
            word_subword (read YMM2_SSE s) (0,128) = simd4 word_add cdgh initcdgh /\
            word_subword (read YMM1_SSE s) (0,128) = simd4 word_add abef initabef)
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM1_SSE; YMM2_SSE] ,, MAYCHANGE [events])`,
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  TRY REFL_TAC);;

Printf.printf "S051_FFZF hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_FEEDFWD_PLUS))
  (List.length(frees(concl SHA256_COMPRESS_HW_FEEDFWD_PLUS)));;
Printf.printf "S051_FFZF_DONE\n%!";;

(* ========================================================================= *)
(* TAIL_SPINE_1BLK: the single-block back-edge control-flow spine, pc+0x2f0    *)
(* -> pc+0x312.  Composes G15_RAW_PLUS ; FEEDFWD_PLUS ; JNE_FALLTHRU with ZF    *)
(* threaded end-to-end for the single-block instantiation (RDX = word 1 on     *)
(* entry to g15's dec).  word_sub (word 1) (word 1) = word 0 so ZF holds and    *)
(* the jne falls through to the epilogue.  YMM9/YMM10 (the feed-forward init    *)
(* saves) ride the frame through G15 (absent from its MAYCHANGE) into           *)
(* FEEDFWD_PLUS.  Phase 6 reuses G15_RAW_PLUS/FEEDFWD_PLUS/JNE_FALLTHRU for the  *)
(* final loop iteration (this fall-through path) vs the taken back-edge.        *)
(* ========================================================================= *)
let SHA256_COMPRESS_HW_TAIL_SPINE_1BLK =
  let g15_1 = SPECL [`pc:num`;`kbase:num`;`kptr:int64`;`mloc:int64`;`mval:int128`;
                     `wk:int128`;`abef:int128`;`cdgh:int128`;
                     `a3:int128`;`a4:int128`;`a5:int128`;`a6:int128`;`word 1:int64`]
               SHA256_COMPRESS_HW_GROUP_STEP4_G15_RAW_PLUS in
  let abef1 = `sha256_rnds2 abef (sha256_rnds2 cdgh abef wk)
                            (word_subword wk (64,64):int128):int128` in
  let cdgh1 = `sha256_rnds2 cdgh abef wk:int128` in
  let ff_1 = SPECL [`pc:num`;`kbase:num`; abef1; cdgh1;
                    `initabef:int128`;`initcdgh:int128`;
                    `word_sub (word 1) (word 1):int64`;`T`]
               SHA256_COMPRESS_HW_FEEDFWD_PLUS in
  prove
 (`!pc kbase (kptr:int64) mloc (mval:int128) wk abef cdgh
     (a3:int128) (a4:int128) (a5:int128) (a6:int128)
     (initabef:int128) (initcdgh:int128).
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x2f0) /\
            read RCX s = kptr /\
            read RDX s = word 1 /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) = (abef:int128) /\
            word_subword (read YMM2_SSE s) (0,128) = (cdgh:int128) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128) /\
            word_subword (read YMM9_SSE s) (0,128) = (initabef:int128) /\
            word_subword (read YMM10_SSE s) (0,128) = (initcdgh:int128))
       (\s. read RIP s = word (pc + 0x312) /\
            word_subword (read YMM2_SSE s) (0,128) =
              simd4 word_add (sha256_rnds2 cdgh abef wk) initcdgh /\
            word_subword (read YMM1_SSE s) (0,128) =
              simd4 word_add
                (sha256_rnds2 abef (sha256_rnds2 cdgh abef wk)
                              (word_subword wk (64,64):int128)) initabef)
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE] ,, MAYCHANGE [RDX] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x302`
   `\s. read RDX s = word_sub (word 1) (word 1):int64 /\
        (read ZF s <=> val (word_sub (word 1) (word 1):int64) = 0) /\
        word_subword (read YMM1_SSE s) (0,128) =
          sha256_rnds2 abef (sha256_rnds2 cdgh abef wk)
                       (word_subword wk (64,64):int128) /\
        word_subword (read YMM2_SSE s) (0,128) = sha256_rnds2 cdgh abef wk /\
        word_subword (read YMM9_SSE s) (0,128) = (initabef:int128) /\
        word_subword (read YMM10_SSE s) (0,128) = (initcdgh:int128)` THEN
  CONJ_TAC THENL
   [MP_TAC(REWRITE_RULE[SOME_FLAGS] g15_1) THEN ASM_REWRITE_TAC[] THEN
    (ENSURES_SUBLEMMA_TAC execup "s" "s'" ORELSE
     ENSURES_SUBLEMMA_REFL_TAC execup "s" "s'") THEN
    ASM_REWRITE_TAC[];
    ENSURES_SEQUENCE_TAC `pc + 0x30c`
     `\s. read ZF s /\
          word_subword (read YMM2_SSE s) (0,128) =
            simd4 word_add (sha256_rnds2 cdgh abef wk) initcdgh /\
          word_subword (read YMM1_SSE s) (0,128) =
            simd4 word_add
              (sha256_rnds2 abef (sha256_rnds2 cdgh abef wk)
                            (word_subword wk (64,64):int128)) initabef` THEN
    CONJ_TAC THENL
     [MP_TAC ff_1 THEN
      REWRITE_TAC[WORD_SUB_REFL; VAL_WORD_0] THEN ASM_REWRITE_TAC[] THEN
      (ENSURES_SUBLEMMA_TAC execup "s" "s'" ORELSE
       ENSURES_SUBLEMMA_REFL_TAC execup "s" "s'") THEN
      ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`pc:num`;`kbase:num`] SHA256_COMPRESS_HW_JNE_FALLTHRU) THEN
      ASM_REWRITE_TAC[] THEN
      (ENSURES_SUBLEMMA_TAC execup "s" "s'" ORELSE
       ENSURES_SUBLEMMA_REFL_TAC execup "s" "s'") THEN
      ASM_REWRITE_TAC[]]]);;

Printf.printf "S051_SPINE hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_TAIL_SPINE_1BLK))
  (List.length(frees(concl SHA256_COMPRESS_HW_TAIL_SPINE_1BLK)));;
Printf.printf "S051_SPINE_DONE\n%!";;

(* ========================================================================= *)
(* Session 052 -- toward the single-block body CORE_BODY_SPEC pc+0x07->0x334. *)
(* Step 1: the RDX-carrying core reaching pc+0x2f0 (BEFORE the dec %rdx@0x2fa),*)
(* so it can chain with TAIL_SPINE_1BLK (which starts at pc+0x2f0).            *)
(*                                                                             *)
(* g15 splits at its K-load: FULL_S_G15 = [K-load leg pc+0x2e4->0x2f0] ;       *)
(* [packed crypto step pc+0x2f0->0x302, which contains the dec].  G15_KLOAD     *)
(* isolates the K-load leg (= FULL_S_G15's own leg-1).  Because NO instruction  *)
(* touches %rdx before the dec at 0x2fa, RDX threads pc+0x07..0x2f0 as a pure   *)
(* frame-rider (MAYCHANGE [RDX] appears only in g15 crypto atoms + composites).  *)
(* ========================================================================= *)

(* --- G15_KLOAD: g15's K-load leg pc+0x2e4 -> pc+0x2f0 (= FULL_S_G15 leg-1). --- *)
let SHA256_COMPRESS_HW_GROUP4_G15_KLOAD = prove
 (`!pc kbase (kptr:int64) (l:int32 list) (kq:int128) a3 a4 a5 a6:int128.
     aligned 16 (word_add (kptr:int64) (word 352))
     ==> ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x2e4) /\
            read RCX s = kptr /\
            read (memory :> bytes128 (word_add kptr (word 352))) s = kq /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (\s. read RIP s = word (pc + 0x2f0) /\
            read RCX s = kptr /\
            read (memory :> bytes128 (word_add kptr (word 352))) s = kq /\
            word_subword (read YMM0_SSE s) (0,128) = simd4 word_add kq a6 /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128))
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[]);;

Printf.printf "S052_G15_KLOAD hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_GROUP4_G15_KLOAD))
  (List.length(frees(concl SHA256_COMPRESS_HW_GROUP4_G15_KLOAD)));;
Printf.printf "S052_G15_KLOAD_DONE\n%!";;

(* --- CORE_TAIL_TO_2F0: tail groups g13 ; g14 ; g15-Kload, pc+0x297 -> pc+0x2f0. *)
(* Mirror of CORE_TAIL3 (S039) with the terminal leg = G15_KLOAD.  RDX threads   *)
(* as a frame-rider (add `read RDX s = rdxin` to PRE / seams / POST; keep RDX out *)
(* of the composed frame).  POST crypto = g14 output (ABEF/CDGH pack of cr...60), *)
(* YMM0 = wk15 = simd4 word_add kq2 a6 -- i.e. exactly G15_RAW_PLUS's PRE @0x2f0. *)
let SHA256_COMPRESS_HW_CORE_TAIL_TO_2F0 =
  let strip_atom th =
    let bod = snd(strip_forall(concl th)) in
    let ens = if is_imp bod then snd(dest_imp bod) else bod in
    let l,c = dest_comb ens in
    let l2,q = dest_comb l in
    let _,p = dest_comb l2 in (p,q,c) in
  let vbyname th n = find (fun v -> name_of v = n) (fst(strip_forall(concl th))) in
  let conjs_of_lam q = let s,body = dest_abs q in s, conjuncts body in
  let contains s sub =
    let ls=String.length s and lsub=String.length sub in
    let rec go i = i+lsub<=ls && (String.sub s i lsub = sub || go(i+1)) in go 0 in
  let is_kread off c =
    is_eq c && contains (string_of_term c) "bytes128"
            && contains (string_of_term c) ("(word " ^ off ^ ")") in
  let kread_for s src_svar src_conjs off =
    vsubst[s,src_svar] (find (is_kread off) src_conjs) in
  let ymm_rhs post nm =
    let _,cs = conjs_of_lam post in
    let hit = find (fun c -> is_eq c && contains (string_of_term(fst(dest_eq c))) nm) cs in
    snd(dest_eq hit) in
  let list_of_abef post =
    let ymm1 = ymm_rhs post "YMM1_SSE" in
    rand(rand(rator(rator(rator ymm1)))) in
  let post_ring q =
    (list_of_abef q, ymm_rhs q "YMM3_SSE", ymm_rhs q "YMM4_SSE",
     ymm_rhs q "YMM5_SSE", ymm_rhs q "YMM6_SSE") in
  let inst_ring_kq atomthm kmap l_v a3_v a4_v a5_v a6_v =
    let base = SPEC_ALL atomthm in
    INST (kmap @
          [ l_v,  vbyname atomthm "l";  a3_v, vbyname atomthm "a3";
            a4_v, vbyname atomthm "a4"; a5_v, vbyname atomthm "a5";
            a6_v, vbyname atomthm "a6" ]) base in
  let vG13 = SHA256_COMPRESS_HW_GROUP4_FULL_S_G13 in
  let g13th = INST [`kq0:int128`, `kq:int128`; `kq1:int128`, `kq1:int128`]
                   (SPEC_ALL vG13) in
  let (pg13,qg13,cg13) = strip_atom g13th in
  let (l13,a313,a413,a513,a613) = post_ring qg13 in
  let g14th = inst_ring_kq SHA256_COMPRESS_HW_GROUP4_FULL_S_G14
                [ `kq1:int128`, `kq:int128`; `kq2:int128`, `kq1:int128` ]
                l13 a313 a413 a513 a613 in
  let (pg14,qg14,cg14) = strip_atom g14th in
  let (l14,a314,a414,a514,a614) = post_ring qg14 in
  let g15kth =
    let base = SPEC_ALL SHA256_COMPRESS_HW_GROUP4_G15_KLOAD in
    INST [ `kq2:int128`, vbyname SHA256_COMPRESS_HW_GROUP4_G15_KLOAD "kq";
           l14,  vbyname SHA256_COMPRESS_HW_GROUP4_G15_KLOAD "l";
           a314, vbyname SHA256_COMPRESS_HW_GROUP4_G15_KLOAD "a3";
           a414, vbyname SHA256_COMPRESS_HW_GROUP4_G15_KLOAD "a4";
           a514, vbyname SHA256_COMPRESS_HW_GROUP4_G15_KLOAD "a5";
           a614, vbyname SHA256_COMPRESS_HW_GROUP4_G15_KLOAD "a6" ] base in
  let (pg15,qg15,cg15) = strip_atom g15kth in
  let svar13,pg13c = conjs_of_lam pg13 in
  let sg14,pg14c = conjs_of_lam pg14 in
  let sg15,pg15c = conjs_of_lam pg15 in
  let sv = `s:x86state` in
  let rdx_rider = `read RDX s = (rdxin:int64)` in
  let mk_rdx s = vsubst[s,sv] rdx_rider in
  let full_frame =
    `MAYCHANGE [RIP] ,,
     MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM5_SSE; YMM6_SSE; YMM7_SSE] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]` in
  let pre_extra = [ kread_for svar13 sg14 pg14c "352" ] in
  let pre_lam = mk_abs(svar13, list_mk_conj (pg13c @ pre_extra @ [mk_rdx svar13])) in
  let sg15q,qg15c = conjs_of_lam qg15 in
  let post_lam = mk_abs(sg15q, list_mk_conj (qg15c @ [mk_rdx sg15q])) in
  let ens_head = rator(rator(rator(snd(dest_imp(snd(strip_forall(concl vG13))))))) in
  let mk_ensures p q c = mk_comb(mk_comb(mk_comb(ens_head,p),q),c) in
  let bvars = [`pc:num`;`kbase:num`;`kptr:int64`;`l:int32 list`;
               `kq0:int128`;`kq1:int128`;`kq2:int128`;
               `a3:int128`;`a4:int128`;`a5:int128`;`a6:int128`;`rdxin:int64`] in
  let hyps = list_mk_conj
    [`aligned 16 (word_add (kptr:int64) (word 288))`;
     `aligned 16 (word_add (kptr:int64) (word 320))`;
     `aligned 16 (word_add (kptr:int64) (word 352))`] in
  let comp_concl = list_mk_forall(bvars, mk_imp(hyps, mk_ensures pre_lam post_lam full_frame)) in
  let seam_core pre =
    let s,cs = conjs_of_lam pre in
    let keep c = not(contains (string_of_term c) "bytes_loaded")
                 && not(contains (string_of_term c) "read RIP") in
    (s, filter keep cs) in
  let seamQ1 = let s,cs = seam_core pg14 in mk_abs(s, list_mk_conj (cs @ [mk_rdx s])) in
  let seamQ2 = let s,cs = seam_core pg15 in mk_abs(s, list_mk_conj (cs @ [mk_rdx s])) in
  prove
   (comp_concl,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[SOME_FLAGS] THEN
    ENSURES_SEQUENCE_TAC `pc + 0x2c2` seamQ1 THEN CONJ_TAC THENL
     [MP_TAC(REWRITE_RULE[SOME_FLAGS] g13th) THEN ASM_REWRITE_TAC[] THEN
      ENSURES_SUBLEMMA_TAC execup "s" "s'" THEN ASM_REWRITE_TAC[];
      ENSURES_SEQUENCE_TAC `pc + 0x2e4` seamQ2 THEN CONJ_TAC THENL
       [MP_TAC(REWRITE_RULE[SOME_FLAGS] g14th) THEN ASM_REWRITE_TAC[] THEN
        (ENSURES_SUBLEMMA_TAC execup "s" "s'" ORELSE
         ENSURES_SUBLEMMA_REFL_TAC execup "s" "s'") THEN ASM_REWRITE_TAC[];
        MP_TAC(REWRITE_RULE[SOME_FLAGS] g15kth) THEN ASM_REWRITE_TAC[] THEN
        (ENSURES_SUBLEMMA_TAC execup "s" "s'" ORELSE
         ENSURES_SUBLEMMA_REFL_TAC execup "s" "s'") THEN ASM_REWRITE_TAC[]]]);;

Printf.printf "S052_CORE_TAIL_TO_2F0 hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_CORE_TAIL_TO_2F0))
  (List.length (frees (concl SHA256_COMPRESS_HW_CORE_TAIL_TO_2F0)));;
Printf.printf "S052_TAIL2F0_DONE\n%!";;

(* ========================================================================= *)
(* Session 052 -- CORE_TO_2F0: the RDX-carrying core pc+0x07 -> pc+0x2f0.      *)
(* Adapts the CORE_ABS composer: head ; R0..R3 ; G8..G12 ; CORE_TAIL_TO_2F0    *)
(* (final leg) -- NO feed-forward, stops at pc+0x2f0 BEFORE the dec %rdx@0x2fa. *)
(* RDX threads as a frame-rider (carried in `riders` alongside YMM9/10/RDI):    *)
(* `read RDX s = rdxin` in the composed PRE, every steady seam, the tail seam,  *)
(* and the POST; RDX is ABSENT from the composed frame (no leg through pc+0x2f0  *)
(* touches it).  POST @pc+0x2f0 = g14 crypto in ABEF/CDGH packs (of CR4(CR4      *)
(* (cr..52)..)..) + YMM0 = wk15 = simd4 word_add kqB msg2-drain + YMM9/10 init   *)
(* riders + RDI=sptr + RDX -- i.e. exactly G15_RAW_PLUS's PRE @pc+0x2f0 (with     *)
(* the ring/riders CORE_BODY_SPEC needs).  hyps=0 frees=0.                        *)
(* ========================================================================= *)
(* S052 step 1c: CORE_TO_2F0 -- the RDX-carrying core pc+0x07 -> pc+0x2f0.       *)
(* Adapts the CORE_ABS composer (L6605): head ; R0..R3 ; G8..G12 ; then          *)
(* CORE_TAIL_TO_2F0 as the FINAL leg (instead of CORE_TAIL3 ; FEEDFWD).  Stops    *)
(* at pc+0x2f0 BEFORE the dec %rdx@0x2fa, so RDX threads as a frame-rider:         *)
(* `read RDX s = rdxin` in composed PRE + the tail seam + POST; RDX absent from    *)
(* the composed frame.  POST = g14 crypto in ABEF/CDGH packs + YMM0 = wk15 +       *)
(* riders (YMM9/10 for feed-forward, RDI=sptr for the exit store) + RDX.           *)

(* ---- term-surgery helpers (self-contained, mirror CORE_ABS) ---- *)
let strip_atom th =
  let bod = snd(strip_forall(concl th)) in
  let ens = if is_imp bod then snd(dest_imp bod) else bod in
  let l,c = dest_comb ens in let l2,q = dest_comb l in
  let _,p = dest_comb l2 in (p,q,c);;
let ens_of th = let bod = snd(strip_forall(concl th)) in
  if is_imp bod then snd(dest_imp bod) else bod;;
let conjs_of_lam q = let s,body = dest_abs q in s, conjuncts body;;
let contains s sub =
  let ls=String.length s and lsub=String.length sub in
  let rec go i = i+lsub<=ls && (String.sub s i lsub = sub || go(i+1)) in go 0;;
let findc sub cs = find (fun c -> contains (string_of_term c) sub) cs;;
let is_kread off c =
  is_eq c && contains (string_of_term c) "bytes128"
          && contains (string_of_term c) ("(word " ^ off ^ ")");;
let kread_in off cs = find (is_kread off) cs;;
let nred_rule = CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV
                          THENC DEPTH_CONV NUM_SUB_CONV THENC DEPTH_CONV NUM_LE_CONV);;
let keepseam c = not(contains (string_of_term c) "bytes_loaded")
                 && not(contains (string_of_term c) "read RIP");;
let sv = `s:x86state`;;
let rebase lam = let s,cs = conjs_of_lam lam in map (vsubst[sv,s]) cs;;

let stlist = `[word_subword (q0:int128) (0,32); word_subword q0 (32,32);
               word_subword q0 (64,32); word_subword q0 (96,32);
               word_subword (q1:int128) (0,32); word_subword q1 (32,32);
               word_subword q1 (64,32); word_subword q1 (96,32)] : int32 list`;;
let kquad n =
  let el j = list_mk_comb(`EL:num->(int32)list->int32`,
               [mk_small_numeral(4*n+j);`sha256_constants:int32 list`]) in
  list_mk_comb(`WQUAD:int32->int32->int32->int32->int128`,[el 0;el 1;el 2;el 3]);;
let steady_leg th g =
  let sp = SPECL [`pc:num`;`kbase:num`;`kptr:int64`;`m:int32 list`;stlist;
                  mk_small_numeral g] th in
  REWRITE_RULE[] (nred_rule (SPEC (kquad (g+1)) sp));;

let head = INST [kquad 4, `kq4:int128`] (SPEC_ALL SHA256_COMPRESS_HW_CORE_HEAD_ABS);;
let steadies =
 [ (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_R0  4),  4, 0x0f4, 0x120;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_R1  5),  5, 0x120, 0x14d;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_R2  6),  6, 0x14d, 0x17a;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_R3  7),  7, 0x17a, 0x1a7;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_G8  8),  8, 0x1a7, 0x1d7;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_G9  9),  9, 0x1d7, 0x207;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_G10 10), 10, 0x207, 0x237;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_G11 11), 11, 0x237, 0x267;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_G12 12), 12, 0x267, 0x297 ];;

(* ---- the tail leg: CORE_TAIL_TO_2F0 instantiated at the g12->tail boundary ---- *)
(* Same instantiation as CORE_ABS's CORE_TAIL3 leg, PLUS rdxin.                    *)
let stlist_cr52 = `sha256_compress_rounds m
    [word_subword (q0:int128) (0,32); word_subword q0 (32,32);
     word_subword q0 (64,32); word_subword q0 (96,32);
     word_subword (q1:int128) (0,32); word_subword q1 (32,32);
     word_subword q1 (64,32); word_subword q1 (96,32)] 52 : int32 list`;;
let tail = SPECL [`pc:num`;`kbase:num`;`kptr:int64`; stlist_cr52;
                  kquad 13; `kqA:int128`; `kqB:int128`;
                  `WWIN m 48:int128`;`WWIN m 52:int128`;
                  `PADP m 40:int128`;`MSG1P m 44:int128`;`rdxin:int64`]
             SHA256_COMPRESS_HW_CORE_TAIL_TO_2F0;;

let (pH,qH,fH) = strip_atom head;;
let pHc = rebase pH and qHc = rebase qH;;
let ymm9  = findc "YMM9_SSE" qHc;;
let ymm10 = findc "YMM10_SSE" qHc;;
let rdi   = findc "read RDI" qHc;;
(* RDX rides EVERY seam (head..tail): it is in the composed PRE, no leg through   *)
(* pc+0x2f0 touches it, and the tail PRE demands it -> carry it as a rider so it  *)
(* threads through the intermediate steady seams too (not just PRE + tail seam).  *)
let rdx_rider0 = `read RDX s = (rdxin:int64)`;;
let riders = [ymm9; ymm10; rdi; rdx_rider0];;

let leg_pre th = rebase (let (p,_,_)=strip_atom th in p);;
let leg_th (th,_,_,_) = th;;
let steady_offs = [32;64;96;128;160;192;224;256;288];;
let tail_offs   = [320;352];;
let allwin = steady_offs @ tail_offs;;
let steady_kterm off =
  let k = off/32 in let leg = List.nth steadies (k-1) in
  kread_in (string_of_int off) (leg_pre (leg_th leg));;
let pTc = rebase (let (p,_,_)=strip_atom tail in p);;
let kterm off =
  if off <= 288 then steady_kterm off else kread_in (string_of_int off) pTc;;

(* RDX rider term over sv *)
let rdx_rider = `read RDX s = (rdxin:int64)`;;

let core cs = filter keepseam cs;;
(* RDX is now carried in `riders`, so drop it from tail contributions to dedup. *)
let no_rdx cs = filter (fun c -> not(contains (string_of_term c) "read RDX")) cs;;
let seam_steady (th,g,_,_) =
  let c = 32*(g-4) in
  let carry = map kterm (filter (fun w -> not(w <= c+32)) allwin) in
  mk_abs(sv, list_mk_conj (core (leg_pre th) @ riders @ carry));;
(* tail seam @0x297: tail PRE-core (RDX removed -> supplied by riders) + riders    *)
(* (YMM9/10/RDI + RDX).  YMM9/10/RDI are NOT in tail PRE so must be carried.        *)
let seam_tail =
  mk_abs(sv, list_mk_conj (no_rdx (core pTc) @ riders));;

(* POST = tail POST-core (RDX removed -> supplied by riders) + riders.  riders     *)
(* YMM9/10/RDI ride (tail drops them from its frame); RDX rides too.               *)
let (_,qTail,_) = strip_atom tail;;
let qTailc = rebase qTail;;
let post_lam = mk_abs(sv, list_mk_conj (no_rdx qTailc @ riders));;

(* composed PRE = head PRE-core + full K window (steady + tail) + RDX rider *)
let pre_lam = mk_abs(sv, list_mk_conj (pHc @ map kterm allwin @ [rdx_rider]));;

let ens_head = rator(rator(rator(ens_of head)));;
let mk_ensures p q c = mk_comb(mk_comb(mk_comb(ens_head,p),q),c);;
(* composed frame = head frame (RIP;RSI + YMM0..10 + flags + events).  NO RDX     *)
(* (every leg through pc+0x2f0 is RDX-neutral).  Strict superset of every leg.    *)
let comp_frame =
  `MAYCHANGE [RIP; RSI] ,,
   MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM5_SSE;
              YMM6_SSE; YMM7_SSE; YMM8_SSE; YMM9_SSE; YMM10_SSE] ,,
   MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;
let bvars = [`pc:num`;`kbase:num`;`kptr:int64`;`m:int32 list`;
             `q0:int128`;`q1:int128`;`mptr:int64`;`sptr:int64`;`kqA:int128`;`kqB:int128`;`rdxin:int64`];;
let comp_hyps = list_mk_conj
 [`aligned 16 (kptr:int64)`;
  `aligned 16 (word_add (kptr:int64) (word 384))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551488))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551520))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551552))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551584))`];;
let comp_concl = list_mk_forall(bvars, mk_imp(comp_hyps, mk_ensures pre_lam post_lam comp_frame));;
Printf.printf "CORE_TO_2F0 concl built. frees(concl)=%d\n%!" (List.length(frees comp_concl));;

let pcterm n = mk_comb(mk_comb(`(+):num->num->num`,`pc:num`), mk_small_numeral n);;
let leg_tac th =
  MP_TAC(REWRITE_RULE[SOME_FLAGS] th) THEN ASM_REWRITE_TAC[] THEN
  (ENSURES_SUBLEMMA_TAC execup "s" "s'" ORELSE
   ENSURES_SUBLEMMA_REFL_TAC execup "s" "s'") THEN ASM_REWRITE_TAC[];;
let rec build entries final = match entries with
  | [] -> leg_tac final
  | (off,seam,disch)::rest ->
      ENSURES_SEQUENCE_TAC (pcterm off) seam THEN
      CONJ_TAC THENL [ leg_tac disch; build rest final ];;

(* entries: 9 steady-entry seams (R0..G12, disch by prev leg) + tail-entry seam    *)
(* @0x297 (disch by G12).  final = tail (CORE_TAIL_TO_2F0).                         *)
let steady_entries =
  let rec go prev = function
    | [] -> []
    | (th,g,e,x)::rest -> (e, seam_steady (th,g,e,x), prev) :: go th rest in
  match steadies with
  | (th0,g0,e0,x0)::rest -> (e0, seam_steady (th0,g0,e0,x0), head) :: go th0 rest
  | [] -> failwith "no steadies";;
let g12th = leg_th (List.nth steadies 8);;
let entries = steady_entries @
  [ 0x297, seam_tail, g12th ];;   (* tail-entry seam, discharged by G12; final=tail *)
Printf.printf "entries=%d (expect 10)\n%!" (List.length entries);;

let mk_align_term n =
  vsubst [mk_small_numeral n, `n:num`]
    `aligned 16 (word_add (kptr:int64) (word n))`;;
let mk_align_sub n =
  let t = mk_align_term n in
  SUBGOAL_THEN t ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORMALIZE_ALIGNED_WORD_CONV t]; ALL_TAC];;

let SHA256_COMPRESS_HW_CORE_TO_2F0 = prove
 (comp_concl,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  EVERY (map mk_align_sub [32;64;96;128;160;192;224;256;288;320;352]) THEN
  build entries tail);;

Printf.printf "S052_CORE_TO_2F0 hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_CORE_TO_2F0))
  (List.length(frees(concl SHA256_COMPRESS_HW_CORE_TO_2F0)));;
Printf.printf "S052_CORE_TO_2F0_DONE\n%!";;

(* ========================================================================= *)
(* Session 052 -- CORE_BODY: the single-block core body pc+0x07 -> pc+0x334.   *)
(* Chains CORE_TO_2F0(rdxin:=word 1) ; TAIL_SPINE_1BLK ; EXIT.  This is the     *)
(* single-block loud-failure K-map test: the whole chain composes only if the   *)
(* g13/g14/g15 K-quad -> EL-offset map is sound and the feed-forward crypto      *)
(* seam holds.  Crypto is kept RAW here (sha256_rnds2 feed-forward WQUADs        *)
(* stored to [rdi]); the spec fold to sha256_block is CORE_BODY_SPEC below.      *)
(* RDX=word 1 (single block) => dec sets ZF => the jne at pc+0x310 falls through  *)
(* to the epilogue.  RDI=sptr rides both seams (absent from SPINE/EXIT frames).  *)
(* ========================================================================= *)
(* S052 step 2: CORE_BODY -- the single-block core body pc+0x07 -> pc+0x334.     *)
(* Chains CORE_TO_2F0(rdxin:=word 1) ; TAIL_SPINE_1BLK ; EXIT.  Crypto kept RAW   *)
(* here (sha256_rnds2 feed-forward form); the spec fold to sha256_block is a       *)
(* separate REWRITE step (CORE_BODY_SPEC), mirroring CORE_ABS -> CORE_ABS_SPEC.    *)
(*                                                                                 *)
(* Seams:                                                                          *)
(*  A @pc+0x2f0: SPINE.PRE.  Instantiate SPINE binders from CORE_TO_2F0.POST:      *)
(*    kptr:=kptr, mloc:=kptr+352, mval:=kqB, wk/abef/cdgh/a3..6 := the CORE_TO_2F0  *)
(*    YMM terms, initabef/initcdgh := the YMM9/10 riders.  RDX=word 1 supplied.    *)
(*  B @pc+0x312: EXIT.PRE.  abef/cdgh := SPINE.POST YMM1/YMM2 (the feed-forward).  *)
(*    RDI=sptr rides the SPINE frame (SPINE doesn't touch RDI).                    *)

let strip_atom th =
  let bod = snd(strip_forall(concl th)) in
  let ens = if is_imp bod then snd(dest_imp bod) else bod in
  let l,c = dest_comb ens in let l2,q = dest_comb l in
  let _,p = dest_comb l2 in (p,q,c);;
let ens_of th = let bod = snd(strip_forall(concl th)) in
  if is_imp bod then snd(dest_imp bod) else bod;;
let conjs_of_lam q = let s,body = dest_abs q in s, conjuncts body;;
let contains s sub =
  let ls=String.length s and lsub=String.length sub in
  let rec go i = i+lsub<=ls && (String.sub s i lsub = sub || go(i+1)) in go 0;;
let findc sub cs = find (fun c -> contains (string_of_term c) sub) cs;;
let sv = `s:x86state`;;
let rebase lam = let s,cs = conjs_of_lam lam in map (vsubst[sv,s]) cs;;
let ymm_rhs cs nm = snd(dest_eq(findc nm cs));;

(* --- CORE_TO_2F0 with rdxin := word 1 --- *)
let core1 = SPEC `word 1:int64`
   (GEN `rdxin:int64` (SPEC_ALL SHA256_COMPRESS_HW_CORE_TO_2F0));;
(* actually SPEC_ALL then re-gen just rdxin is awkward; instead INST it: *)
let core1 = INST [`word 1:int64`,`rdxin:int64`] (SPEC_ALL SHA256_COMPRESS_HW_CORE_TO_2F0);;
let (pc0,qc0,fc0) = strip_atom core1;;
let qc0c = rebase qc0;;
(* harvest CORE_TO_2F0 POST occupants for SPINE instantiation *)
let wk_t   = ymm_rhs qc0c "YMM0_SSE";;
let abef_t = ymm_rhs qc0c "YMM1_SSE";;
let cdgh_t = ymm_rhs qc0c "YMM2_SSE";;
let a3_t   = ymm_rhs qc0c "YMM3_SSE";;
let a4_t   = ymm_rhs qc0c "YMM4_SSE";;
let a5_t   = ymm_rhs qc0c "YMM5_SSE";;
let a6_t   = ymm_rhs qc0c "YMM6_SSE";;
let ia_t   = ymm_rhs qc0c "YMM9_SSE";;
let ic_t   = ymm_rhs qc0c "YMM10_SSE";;
(* mval = the K read @352 in CORE_TO_2F0 POST *)
let kq352_t = snd(dest_eq(find (fun c -> contains (string_of_term c) "(word 352)")
                            (filter is_eq qc0c)));;

(* --- SPINE instantiated at the seam --- *)
let spine = SPECL [`pc:num`;`kbase:num`;`kptr:int64`;
                   `word_add kptr (word 352):int64`; kq352_t;
                   wk_t; abef_t; cdgh_t; a3_t; a4_t; a5_t; a6_t; ia_t; ic_t]
              SHA256_COMPRESS_HW_TAIL_SPINE_1BLK;;
let (ps,qs,fs) = strip_atom spine;;
let qsc = rebase qs;;
let sp_abef = ymm_rhs qsc "YMM1_SSE";;   (* SPINE POST YMM1 = feed-forward abef *)
let sp_cdgh = ymm_rhs qsc "YMM2_SSE";;   (* SPINE POST YMM2 = feed-forward cdgh *)

(* --- EXIT instantiated at the seam (abef/cdgh := SPINE feed-forward) --- *)
let exitth = SPECL [`pc:num`;`kbase:num`;`sptr:int64`; sp_abef; sp_cdgh]
               SHA256_COMPRESS_HW_EXIT;;
let (pe,qe,fe) = strip_atom exitth;;
let qec = rebase qe;;

(* --- composed statement pc+0x07 -> pc+0x334 --- *)
(* PRE = CORE_TO_2F0.PRE (rdxin=1).  POST = EXIT.POST (the two memory stores).     *)
let pre_lam = pc0;;
let post_lam = qe;;
let keepseam c = not(contains (string_of_term c) "bytes_loaded")
                 && not(contains (string_of_term c) "read RIP");;
let core cs = filter keepseam cs;;

let ens_head = rator(rator(rator(ens_of core1)));;
let mk_ensures p q c = mk_comb(mk_comb(mk_comb(ens_head,p),q),c);;
(* composed frame = CORE_TO_2F0 frame (+) SPINE frame (+) EXIT frame.  Union.      *)
let comp_frame =
  `MAYCHANGE [RIP; RSI; RDX] ,,
   MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM5_SSE;
              YMM6_SSE; YMM7_SSE; YMM8_SSE; YMM9_SSE; YMM10_SSE] ,,
   MAYCHANGE [memory :> bytes128 sptr;
              memory :> bytes128 (word_add sptr (word 16))] ,,
   MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;
let bvars = [`pc:num`;`kbase:num`;`kptr:int64`;`m:int32 list`;
             `q0:int128`;`q1:int128`;`mptr:int64`;`sptr:int64`;`kqA:int128`;`kqB:int128`];;
(* hyps = CORE_TO_2F0 hyps + EXIT's nonoverlapping *)
let comp_hyps = list_mk_conj
 [`aligned 16 (kptr:int64)`;
  `aligned 16 (word_add (kptr:int64) (word 384))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551488))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551520))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551552))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551584))`;
  `nonoverlapping (word pc, 825) (sptr:int64, 32)`];;
let comp_concl = list_mk_forall(bvars, mk_imp(comp_hyps, mk_ensures pre_lam post_lam comp_frame));;
Printf.printf "CORE_BODY concl built. frees(concl)=%d\n%!" (List.length(frees comp_concl));;

(* seams: seamA @0x2f0 = SPINE PRE-core + RDI rider; seamB @0x312 = EXIT PRE-core. *)
(* RDI must ride BOTH seams: it is absent from SPINE's and EXIT's frames, so for    *)
(* SPINE to carry RDI=sptr from seamA to seamB (which EXIT's PRE needs), seamA must *)
(* already state it (an out-of-frame rider only rides if the seam carries it).      *)
let seamA = mk_abs(sv, list_mk_conj (core (rebase ps) @ [`read RDI s = sptr`]));;
let seamB = mk_abs(sv, list_mk_conj (core (rebase pe) @ [`read RDI s = sptr`]));;

let pcterm n = mk_comb(mk_comb(`(+):num->num->num`,`pc:num`), mk_small_numeral n);;
let leg_tac th =
  MP_TAC(REWRITE_RULE[SOME_FLAGS] th) THEN ASM_REWRITE_TAC[] THEN
  (ENSURES_SUBLEMMA_TAC execup "s" "s'" ORELSE
   ENSURES_SUBLEMMA_REFL_TAC execup "s" "s'") THEN ASM_REWRITE_TAC[];;

let SHA256_COMPRESS_HW_CORE_BODY = prove
 (comp_concl,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC (pcterm 0x2f0) seamA THEN CONJ_TAC THENL
   [leg_tac core1;
    ENSURES_SEQUENCE_TAC (pcterm 0x312) seamB THEN CONJ_TAC THENL
     [leg_tac spine;
      leg_tac exitth]]);;

Printf.printf "S052_CORE_BODY hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_CORE_BODY))
  (List.length(frees(concl SHA256_COMPRESS_HW_CORE_BODY)));;
Printf.printf "S052_CORE_BODY_DONE\n%!";;

(* ========================================================================= *)
(* Session 052 -- CORE_BODY_SPEC: the SPEC-form single-block body.            *)
(* Folds CORE_BODY's raw-crypto store (sha256_rnds2 feed-forward of the g15    *)
(* group) to the natural-order FIPS 180-4 state stored to [rdi]/[rdi+16]:      *)
(*   [rdi]    = WQUAD (EL 0 blk)(EL 1 blk)(EL 2 blk)(EL 3 blk)   {A,B,C,D}     *)
(*   [rdi+16] = WQUAD (EL 4 blk)(EL 5 blk)(EL 6 blk)(EL 7 blk)   {E,F,G,H}     *)
(*   where blk = sha256_block m [q0 lanes; q1 lanes] and [q0;q1] is the        *)
(*   ABEF/CDGH-loaded initial state.  This is the genuine block-function       *)
(*   connection for a single block (RDX = 1).                                  *)
(*                                                                             *)
(* Fold recipe = CORE_ABS_SPEC's (kqA:=WQUAD(EL 56..59), kqB:=WQUAD(EL 60..63);*)
(* wring40/padp44/wring44; cr52..cr60; SIMD4_ADD_ABEF/CDGH; GSYM BLOCK_ELS)     *)
(* PLUS the g15 raw-group-advance fold that CORE_ABS_SPEC did not need (its     *)
(* feed-forward path had already advanced g15): SHA256_RNDS2_GROUP_ADVANCE      *)
(* (GA1 then GA2, sequential -- GA2 consumes GA1's ABEF_PACK(two)) + ATCF       *)
(* (ABEF_PACK(two)=CDGH_PACK(four) for the CDGH lane) + GSYM CR4 + cr60, all    *)
(* applied BEFORE the CORE_ABS_SPEC rules with cr52/cr56 collapsing the g14      *)
(* output to cr60 so GROUP_ADVANCE's l:=cr60 matches.  Plus ABEF/CDGH_PACK       *)
(* subword lemmas to resolve the epilogue store's word_subword extractions.     *)
(* ========================================================================= *)
(* S052 step 2b (v2): CORE_BODY_SPEC with the g15 raw-rnds2 crypto fold added.    *)
(* CORE_BODY stores the RAW g15 crypto (sha256_rnds2 of ABEF_PACK(cr60)); to reach *)
(* sha256_block I must first fold that raw group step to ABEF_PACK(cr64) -- exactly *)
(* what G15_PACKED does via SHA256_RNDS2_GROUP_ADVANCE + ABEF_TWO_IS_CDGH_FOUR --   *)
(* then the CORE_ABS_SPEC rules (cr52/56/60 + wring + SIMD4_ADD + BLOCK_ELS) apply. *)

let ABEF_PACK_SUBWORDS = prove
 (`!a b e f:int32.
     word_subword (ABEF_PACK a b e f) (96,32) = a /\
     word_subword (ABEF_PACK a b e f) (64,32) = b /\
     word_subword (ABEF_PACK a b e f) (32,32) = e /\
     word_subword (ABEF_PACK a b e f) (0,32) = f`,
  REWRITE_TAC[ABEF_PACK] THEN CONV_TAC WORD_BLAST);;
let CDGH_PACK_SUBWORDS = prove
 (`!c d g h:int32.
     word_subword (CDGH_PACK c d g h) (96,32) = c /\
     word_subword (CDGH_PACK c d g h) (64,32) = d /\
     word_subword (CDGH_PACK c d g h) (32,32) = g /\
     word_subword (CDGH_PACK c d g h) (0,32) = h`,
  REWRITE_TAC[CDGH_PACK] THEN CONV_TAC WORD_BLAST);;

let SHA256_COMPRESS_HW_CORE_BODY_SPEC =
  let stl = `[word_subword (q0:int128) (0,32); word_subword q0 (32,32);
              word_subword q0 (64,32); word_subword q0 (96,32);
              word_subword (q1:int128) (0,32); word_subword q1 (32,32);
              word_subword q1 (64,32); word_subword q1 (96,32)] : int32 list` in
  let kqA_val = `WQUAD (EL 56 sha256_constants) (EL 57 sha256_constants)
                       (EL 58 sha256_constants) (EL 59 sha256_constants) : int128` in
  let kqB_val = `WQUAD (EL 60 sha256_constants) (EL 61 sha256_constants)
                       (EL 62 sha256_constants) (EL 63 sha256_constants) : int128` in
  let body' = INST [kqA_val, `kqA:int128`; kqB_val, `kqB:int128`]
                (SPEC_ALL SHA256_COMPRESS_HW_CORE_BODY) in
  let nred_cr  = CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV) in
  let nred_off = CONV_RULE(DEPTH_CONV NUM_ADD_CONV) in
  let cr_step g = nred_cr (SPECL [`m:int32 list`; stl; mk_small_numeral g]
                            CR4_SPEC_STEP_WWIN) in
  let cr52 = cr_step 13 and cr56 = cr_step 14 and cr60 = cr_step 15 in
  let wring40 = nred_off (SPECL [`m:int32 list`; `40`] WRING_WWIN) in
  let wring44 = nred_off (SPECL [`m:int32 list`; `44`] WRING_WWIN) in
  let padp44  = GSYM(nred_off (SPECL [`m:int32 list`; `44`] PADP)) in
  (* STAGE A: fold the g15 schedule so wk15 = simd4 word_add kqB (WWIN 60), AND      *)
  (* collapse the g14 crypto output CR4(CR4(cr52)(wk52))(wk56) -> cr60 via cr52,cr56 *)
  (* (g13,g14 CR4 steps) so GROUP_ADVANCE's l:=cr60 will match the ABEF_PACK arg.    *)
  let stepA = REWRITE_RULE[wring40; padp44; wring44; cr52; cr56] body' in
  (* STAGE B: fold the raw g15 group advance to CR4 form via G15_PACKED's method:   *)
  (* GROUP_ADVANCE (l:=cr60, wk:=wk15) turns the two rnds2 into ABEF_PACK(four), and *)
  (* ATCF makes ABEF_PACK(cr60) = CDGH_PACK(...) so the CDGH input matches.  Package *)
  (* these as the reverse of G15_PACKED's rewrite -- easier: use CR4 def + the two   *)
  (* CONJUNCTs directly.  cr60-as-list l, wk15 concrete.                             *)
  let l60 = `sha256_compress_rounds m
      [word_subword (q0:int128) (0,32); word_subword q0 (32,32);
       word_subword q0 (64,32); word_subword q0 (96,32);
       word_subword (q1:int128) (0,32); word_subword q1 (32,32);
       word_subword q1 (64,32); word_subword q1 (96,32)] 60 : int32 list` in
  let wk15 = `simd4 word_add
     (WQUAD (EL 60 sha256_constants) (EL 61 sha256_constants)
            (EL 62 sha256_constants) (EL 63 sha256_constants))
     (WWIN m 60) : int128` in
  let GA = CONV_RULE(TOP_DEPTH_CONV let_CONV)
             (SPECL [l60; wk15] SHA256_RNDS2_GROUP_ADVANCE) in
  let GA1 = CONJUNCT1 GA and GA2 = CONJUNCT2 GA in
  (* ATCF: ABEF_PACK(two) = CDGH_PACK(four) -- the CDGH (YMM2) output of g15 comes    *)
  (* out as ABEF_PACK(two) from GA1, and this identity restores the CDGH_PACK(four)   *)
  (* form so the CDGH lanes fold to cr64 too (mirrors G15_PACKED's ATCF use).         *)
  let ATCF = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [l60;
             `word_subword (wk15v:int128) (0,32):int32`; `word_subword (wk15v:int128) (32,32):int32`;
             `word_subword (wk15v:int128) (64,32):int32`; `word_subword (wk15v:int128) (96,32):int32`]
            ABEF_TWO_IS_CDGH_FOUR) in
  let ATCF = INST [wk15, `wk15v:int128`] ATCF in
  (* GROUP_ADVANCE rewrites raw->packed.  GA1 gives ABEF_PACK(two) (the CDGH out),    *)
  (* GA2 gives ABEF_PACK(four) (the ABEF out).  Apply GA2 first, then ATCF turns the  *)
  (* leftover ABEF_PACK(two) into CDGH_PACK(four), then GA1 is not needed -- but keep *)
  (* both for safety.  four = the CR4 nest; fold via GSYM CR4 then cr60.              *)
  (* Order matters: GA1 then GA2 first (GA2 consumes GA1's ABEF_PACK(two) output);   *)
  (* only THEN ATCF, to fold the standalone CDGH-slot ABEF_PACK(two) -> CDGH_PACK.    *)
  let stepB0 = REWRITE_RULE[GA1] stepA in
  let stepB1 = REWRITE_RULE[GA2] stepB0 in
  let stepB  = REWRITE_RULE[ATCF] stepB1 in
  let stepC = REWRITE_RULE[cr60] (REWRITE_RULE[GSYM CR4] stepB) in
  let step2 = REWRITE_RULE[SIMD4_ADD_ABEF; SIMD4_ADD_CDGH] stepC in
  let step3 = REWRITE_RULE[GSYM SHA256_COMPRESS_HW_BLOCK_ELS] step2 in
  let step4 = REWRITE_RULE[ABEF_PACK_SUBWORDS; CDGH_PACK_SUBWORDS] step3 in
  GEN_ALL step4;;

Printf.printf "S052_CORE_BODY_SPEC hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_CORE_BODY_SPEC))
  (List.length(frees(concl SHA256_COMPRESS_HW_CORE_BODY_SPEC)));;
Printf.printf "S052_CORE_BODY_SPEC_DONE\n%!";;

(* ========================================================================= *)
(* Session 053 -- PHASE 6: the multi-block do-while loop -> CORE_CORRECT.      *)
(*                                                                             *)
(* Control flow (tmc pc = obj pc - 4): the entry sequence pc+0x07 -> pc+0x38   *)
(* (ENTRY_REPACK: state load [rdi] -> ABEF/CDGH regs YMM1/YMM2, mask -> YMM7    *)
(* AND saved to YMM8) runs ONCE.  pc+0x38 is the LOOP HEAD (the `jne` target).  *)
(* The loop body pc+0x38 -> jne@pc+0x30c then either takes the back-edge to     *)
(* pc+0x38 (RDX != 0) or falls through to the epilogue EXIT (pc+0x312->0x334).  *)
(*                                                                             *)
(* So the single-block CORE_BODY(_SPEC) (pc+0x07->0x334) fuses the entry INTO    *)
(* the body; for the multi-block loop we must FACTOR THE ENTRY OUT and build a   *)
(* loop-body lemma that starts at pc+0x38 with the running state already in the  *)
(* ABEF/CDGH registers (not memory).  HEAD38_RAW is the first piece: the head    *)
(* of the loop body, pc+0x38 -> pc+0xf4 = HEAD_MSGLOAD0 ; CORE_HEAD_CRYPTO,       *)
(* parameterized by an ABSTRACT state list l (YMM1 = ABEF_PACK(EL0/1/4/5 l),      *)
(* YMM2 = CDGH_PACK(EL2/3/6/7 l)) so the loop invariant can bind l to the         *)
(* running hash state sha256_hash_blocks m_fn H i.  Mirrors CORE_HEAD but drops   *)
(* the ENTRY_REPACK leg (which is the once-only entry).                          *)
(* ========================================================================= *)

let h38_strip_atom th =
  let bod = snd(strip_forall(concl th)) in
  let ens = if is_imp bod then snd(dest_imp bod) else bod in
  let l,c = dest_comb ens in let l2,q = dest_comb l in let _,p = dest_comb l2 in (p,q,c);;
let h38_conjs q = let s,body = dest_abs q in s, conjuncts body;;
let h38_contains s sub =
  let ls=String.length s and lsub=String.length sub in
  let rec go i = i+lsub<=ls && (String.sub s i lsub = sub || go(i+1)) in go 0;;
let h38_find sub cs = find (fun c -> h38_contains (string_of_term c) sub) cs;;

let masklit = `word 16018520953223639909183530438118932995 : int128`;;
let brm0 = `usimd4 word_bytereverse (m0:int128) : int128`;;
let l_state = `l:int32 list`;;

let msg_i = SPECL [`pc:num`;`kbase:num`;`kptr:int64`;`mptr:int64`;
                   `m0:int128`;`m1:int128`;`m2:int128`;`m3:int128`]
              SHA256_COMPRESS_HW_HEAD_MSGLOAD0;;
let crypto_i0 = SPECL [`pc:num`;`kbase:num`;`kptr:int64`;`mptr:int64`; l_state;
                       `kq0:int128`;`kq1:int128`;`kq2:int128`;`kq3:int128`;`kq4:int128`;
                       brm0; `m1:int128`;`m2:int128`;`m3:int128`]
                  SHA256_COMPRESS_HW_CORE_HEAD_CRYPTO;;
let crypto_i = crypto_i0;;

let (peM,poM,frM) = h38_strip_atom msg_i;;
let sv, peMc = h38_conjs peM;;
let rebase src cs = let s,_ = h38_conjs src in map (vsubst[sv,s]) cs;;
let poMc = rebase poM (snd(h38_conjs poM));;
let (peC,poC,frC) = h38_strip_atom crypto_i;;
let peCc = rebase peC (snd(h38_conjs peC));;
let poCc = rebase poC (snd(h38_conjs poC));;

let ymm1_pack = h38_find "YMM1_SSE" peCc;;   (* ABEF_PACK(EL0/1/4/5 l) *)
let ymm2_pack = h38_find "YMM2_SSE" peCc;;   (* CDGH_PACK(EL2/3/6/7 l) *)
let k_reads = filter (fun c -> h38_contains (string_of_term c) "read (memory"
                 && (h38_contains (string_of_term c) "bytes128 kptr)"
                     || h38_contains (string_of_term c) "18446744073709551")) peCc;;

let pre_lam = mk_abs(sv, list_mk_conj (peMc @ [ymm1_pack; ymm2_pack] @ k_reads));;
let post_lam = mk_abs(sv, list_mk_conj poCc);;
let comp_frame =
 `MAYCHANGE [RIP; RSI] ,,
  MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM5_SSE;
             YMM6_SSE; YMM7_SSE; YMM9_SSE; YMM10_SSE] ,,
  MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;
let comp_hyps = list_mk_conj
 [`aligned 16 (word_add (kptr:int64) (word 18446744073709551488))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551520))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551552))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551584))`];;
let ens_head = rator(rator(rator(snd(dest_imp(snd(strip_forall(concl
                 SHA256_COMPRESS_HW_CORE_HEAD_CRYPTO)))))));;
let mk_ensures p q c = mk_comb(mk_comb(mk_comb(ens_head,p),q),c);;
let bvars = [`pc:num`;`kbase:num`;`kptr:int64`;`mptr:int64`;`l:int32 list`;
             `m0:int128`;`m1:int128`;`m2:int128`;`m3:int128`;
             `kq0:int128`;`kq1:int128`;`kq2:int128`;`kq3:int128`;`kq4:int128`];;
let comp_concl = list_mk_forall(bvars, mk_imp(comp_hyps, mk_ensures pre_lam post_lam comp_frame));;

let keep c = not(h38_contains (string_of_term c) "bytes_loaded")
             && not(h38_contains (string_of_term c) "read RIP");;
let core cs = filter keep cs;;
let seamQ1 = mk_abs(sv, list_mk_conj (core peCc));;

let SHA256_COMPRESS_HW_HEAD38_RAW = prove
 (comp_concl,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x50` seamQ1 THEN CONJ_TAC THENL
   [MP_TAC msg_i THEN ASM_REWRITE_TAC[] THEN
    ENSURES_SUBLEMMA_TAC execup "s" "s'" THEN ASM_REWRITE_TAC[];
    MP_TAC(REWRITE_RULE[SOME_FLAGS] crypto_i) THEN ASM_REWRITE_TAC[] THEN
    ENSURES_SUBLEMMA_TAC execup "s" "s'" THEN ASM_REWRITE_TAC[]]);;

Printf.printf "S053_HEAD38_RAW hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_HEAD38_RAW))
  (List.length (frees (concl SHA256_COMPRESS_HW_HEAD38_RAW)));;
Printf.printf "S053_HEAD38_RAW_DONE\n%!";;

(* ------------------------------------------------------------------------- *)
(* HEAD38_ABS: HEAD38_RAW's POST @pc+0xf4 restated in the OPAQUE SPEC form,    *)
(* exactly the shape of SPEC_STEP_R0[g:=4]'s PRE (crypto = compress_rounds     *)
(* m l 16; ring YMM3=WWIN 16, YMM4=PADP 4, YMM5=MSG1P 8, YMM6=WWIN 12), so     *)
(* the loop-body composer chains HEAD38_ABS -> the steady SPEC_STEP layer with *)
(* only the trivial 16 = 4*4 normalization (identical to CORE_HEAD_ABS's role  *)
(* in CORE_TO_2F0, but starting from pc+0x38 with state in registers).         *)
(*                                                                             *)
(* Derivation = CORE_HEAD_ABS's (S046), applied to HEAD38_RAW: INST the raw    *)
(* message-quad binders m_i := WQUAD(wbr(EL(4i+j) m)) and K-quad binders       *)
(* kq_i := WQUAD(EL(4i+j) consts), then rewrite the byteswapped POST occupants  *)
(* via HEAD_MSG_BRIDGE (b_i = WWIN(4i)) + the head folds HEAD_CRYPTO_FOLD /     *)
(* HEAD_YMM3/4/5.  Here the working state is the abstract list l directly (not  *)
(* [q0/q1 subwords]), so YMM9/YMM10 = ABEF/CDGH_PACK(EL.. l) are the running    *)
(* state's feed-forward saves.  FOLD-ORDER TRAP: YMM4 before YMM3.             *)
(* ------------------------------------------------------------------------- *)
let SHA256_COMPRESS_HW_HEAD38_ABS =
  let e j i = mk_comb(`word_bytereverse:int32->int32`,
      list_mk_comb(`EL:num->(int32)list->int32`,[mk_small_numeral(4*i+j);`m:int32 list`])) in
  let rawquad i = list_mk_comb(`WQUAD:int32->int32->int32->int32->int128`,
                    [e 0 i;e 1 i;e 2 i;e 3 i]) in
  let kc j i = list_mk_comb(`EL:num->(int32)list->int32`,
      [mk_small_numeral(4*i+j);`sha256_constants:int32 list`]) in
  let kquad i = list_mk_comb(`WQUAD:int32->int32->int32->int32->int128`,
                  [kc 0 i;kc 1 i;kc 2 i;kc 3 i]) in
  let subs = [ rawquad 0,`m0:int128`; rawquad 1,`m1:int128`;
               rawquad 2,`m2:int128`; rawquad 3,`m3:int128`;
               kquad 0,`kq0:int128`; kquad 1,`kq1:int128`;
               kquad 2,`kq2:int128`; kquad 3,`kq3:int128` ] in
  let headI = INST subs (SPEC_ALL SHA256_COMPRESS_HW_HEAD38_RAW) in
  let bfold i =
    let br = SPECL [`m:int32 list`; mk_small_numeral i] SHA256_COMPRESS_HW_HEAD_MSG_BRIDGE in
    let br = MP br (ARITH_RULE(mk_comb(mk_comb(`(<):num->num->bool`,mk_small_numeral i),`4`))) in
    CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV) br in
  let bthms = map bfold [0;1;2;3] in
  let stl = `l:int32 list` in
  let wwin i = list_mk_comb(`WWIN:(int32)list->num->int128`,
                 [`m:int32 list`;mk_small_numeral(4*i)]) in
  let cryptofold =
    let th = INST ([ stl,`st:int32 list` ] @
                   (map (fun i -> kquad i, mk_var("kq"^string_of_int i,`:int128`)) [0;1;2;3]) @
                   (map (fun i -> wwin i, mk_var("b"^string_of_int i,`:int128`)) [0;1;2;3]))
              (SPEC_ALL SHA256_COMPRESS_HW_HEAD_CRYPTO_FOLD) in
    MP th (end_itlist CONJ (map REFL ((map kquad [0;1;2;3]) @ (map wwin [0;1;2;3])))) in
  let ymm3fold =
    let th = INST (map (fun i -> wwin i, mk_var("b"^string_of_int i,`:int128`)) [0;1;2;3])
              (SPEC_ALL SHA256_COMPRESS_HW_HEAD_YMM3) in
    MP th (end_itlist CONJ (map (fun i -> REFL(wwin i)) [0;1;2;3])) in
  let ymm4fold =
    let th = INST (map (fun i -> wwin i, mk_var("b"^string_of_int i,`:int128`)) [0;1;2;3])
              (SPEC_ALL SHA256_COMPRESS_HW_HEAD_YMM4) in
    MP th (end_itlist CONJ (map (fun i -> REFL(wwin i)) [0;1;2;3])) in
  let ymm5fold =
    let th = INST [wwin 2,`b2:int128`; wwin 3,`b3:int128`]
              (SPEC_ALL SHA256_COMPRESS_HW_HEAD_YMM5) in
    MP th (CONJ (REFL(wwin 2)) (REFL(wwin 3))) in
  let headB   = REWRITE_RULE bthms headI in
  let headB4  = GEN_REWRITE_RULE (RAND_CONV o TOP_DEPTH_CONV) [ymm4fold] headB in
  GEN_ALL(REWRITE_RULE [cryptofold; ymm3fold; ymm5fold] headB4);;

Printf.printf "S053_HEAD38_ABS hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_HEAD38_ABS))
  (List.length(frees(concl SHA256_COMPRESS_HW_HEAD38_ABS)));;
Printf.printf "S053_HEAD38_ABS_DONE\n%!";;

(* ------------------------------------------------------------------------- *)
(* MASK THREADING for the loop body.  The byteswap mask lives in TWO xmm regs: *)
(*  - YMM8 = mask: set ONCE by ENTRY_REPACK (movdqa %xmm7,%xmm8 @ obj 0x2b);   *)
(*    NEVER written again (YMM8_SSE appears in a MAYCHANGE frame only in        *)
(*    ENTRY_REPACK), so it rides the whole loop body as a pure frame-rider.     *)
(*  - YMM7 = mask: consumed by the head pshufb byteswaps and clobbered as       *)
(*    schedule-ring scratch throughout the groups, then RE-ESTABLISHED by       *)
(*    `movdqa %xmm8,%xmm7` at tmc pc+0x2db (inside g14), untouched afterwards.   *)
(* So at the back-edge (pc+0x30c) YMM7 = YMM8 = mask, and the loop invariant     *)
(* @pc+0x38 needs BOTH (the next iteration's pshufb reads YMM7).                 *)
(*                                                                             *)
(* G14_RAW_PLUS strengthens G14_RAW to carry YMM8 = mask (PRE) and expose       *)
(* YMM7 = mask (POST) -- exactly mirroring how G15_RAW_PLUS threaded RDX/ZF.    *)
(* ------------------------------------------------------------------------- *)
let SHA256_COMPRESS_HW_GROUP_STEP4_G14_RAW_PLUS = prove
 (`!pc kbase (kptr:int64) mloc (mval:int128) wk abef cdgh (a3:int128) (a4:int128) (a5:int128) (a6:int128) (mask:int128).
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x2ce) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) = (abef:int128) /\
            word_subword (read YMM2_SSE s) (0,128) = (cdgh:int128) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128) /\
            word_subword (read YMM8_SSE s) (0,128) = (mask:int128))
       (\s. read RIP s = word (pc + 0x2e4) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM2_SSE s) (0,128) = sha256_rnds2 cdgh abef wk /\
            word_subword (read YMM1_SSE s) (0,128) =
              sha256_rnds2 abef (sha256_rnds2 cdgh abef wk)
                           (word_subword wk (64,64) : int128) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = sha256_msg2 a6 a5 /\
            word_subword (read YMM7_SSE s) (0,128) = (mask:int128) /\
            word_subword (read YMM8_SSE s) (0,128) = (mask:int128))
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM6_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s5" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC SHA256_RNDS2_WK_CONG THEN CONJ_TAC THEN
      CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC) THEN
  TRY REFL_TAC);;
Printf.printf "S053_G14_RAW_PLUS hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_GROUP_STEP4_G14_RAW_PLUS))
  (List.length (frees (concl SHA256_COMPRESS_HW_GROUP_STEP4_G14_RAW_PLUS)));;
Printf.printf "S053_G14_RAW_PLUS_DONE\n%!";;

(* G14_PACKED_PLUS: G14_RAW_PLUS rewritten to CR4/pack form (mask threaded),  *)
(* mirroring G14_PACKED's GROUP_ADVANCE + ATCF rewrite over G14_RAW_PLUS.      *)
let SHA256_COMPRESS_HW_GROUP_STEP4_G14_PACKED_PLUS = prove
 (`!pc kbase (kptr:int64) mloc (mval:int128) (l:int32 list) (wk:int128) (a3:int128) (a4:int128) (a5:int128) (a6:int128) (mask:int128).
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x2ce) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM0_SSE s) (0,128) = (wk:int128) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128) /\
            word_subword (read YMM8_SSE s) (0,128) = (mask:int128))
       (\s. read RIP s = word (pc + 0x2e4) /\
            read RCX s = kptr /\
            read (memory :> bytes128 mloc) s = mval /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (CR4 l wk)) (EL 3 (CR4 l wk))
                        (EL 6 (CR4 l wk)) (EL 7 (CR4 l wk)) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (CR4 l wk)) (EL 1 (CR4 l wk))
                        (EL 4 (CR4 l wk)) (EL 5 (CR4 l wk)) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = sha256_msg2 a6 a5 /\
            word_subword (read YMM7_SSE s) (0,128) = (mask:int128) /\
            word_subword (read YMM8_SSE s) (0,128) = (mask:int128))
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM6_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  let GA = CONV_RULE(TOP_DEPTH_CONV let_CONV)
             (SPECL [`l:int32 list`; `wk:int128`] SHA256_RNDS2_GROUP_ADVANCE) in
  let GA1 = CONJUNCT1 GA and GA2 = CONJUNCT2 GA in
  let ATCF = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`l:int32 list`;
             `word_subword wk (0,32):int32`; `word_subword wk (32,32):int32`;
             `word_subword wk (64,32):int32`; `word_subword wk (96,32):int32`]
            ABEF_TWO_IS_CDGH_FOUR) in
  REPEAT GEN_TAC THEN REWRITE_TAC[CR4] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA2] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM ATCF] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA1] THEN
  MATCH_ACCEPT_TAC SHA256_COMPRESS_HW_GROUP_STEP4_G14_RAW_PLUS);;
Printf.printf "S053_G14_PACKED_PLUS hyps=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_GROUP_STEP4_G14_PACKED_PLUS));;

(* FULL_S_G14_PLUS: full g14 pc+0x2c2->0x2e4 with the byteswap mask threaded.  *)
(* Leg-1 = K-load (movdqa[rcx+0x140]+paddd xmm5) by stepping (YMM8=mask rides); *)
(* leg-2 = G14_PACKED_PLUS.  Same shape as FULL_S_G14 + YMM8 PRE-rider +         *)
(* YMM7=YMM8=mask in POST.  Used by CORE_TAIL_TO_2F0_PLUS for the loop body.     *)
let SHA256_COMPRESS_HW_GROUP4_FULL_S_G14_PLUS = prove
 (`!pc kbase (kptr:int64) (l:int32 list) (kq:int128) (kq1:int128) a3 a4 a5 a6 (mask:int128):int128.
     aligned 16 (word_add (kptr:int64) (word 320))
     ==> ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x2c2) /\
            read RCX s = kptr /\
            read (memory :> bytes128 (word_add kptr (word 320))) s = kq /\
            read (memory :> bytes128 (word_add kptr (word 352))) s = kq1 /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = (a6:int128) /\
            word_subword (read YMM8_SSE s) (0,128) = (mask:int128))
       (\s. read RIP s = word (pc + 0x2e4) /\
            read RCX s = kptr /\
            read (memory :> bytes128 (word_add kptr (word 352))) s = kq1 /\
            word_subword (read YMM2_SSE s) (0,128) =
              CDGH_PACK (EL 2 (CR4 l (simd4 word_add kq a5)))
                        (EL 3 (CR4 l (simd4 word_add kq a5)))
                        (EL 6 (CR4 l (simd4 word_add kq a5)))
                        (EL 7 (CR4 l (simd4 word_add kq a5))) /\
            word_subword (read YMM1_SSE s) (0,128) =
              ABEF_PACK (EL 0 (CR4 l (simd4 word_add kq a5)))
                        (EL 1 (CR4 l (simd4 word_add kq a5)))
                        (EL 4 (CR4 l (simd4 word_add kq a5)))
                        (EL 5 (CR4 l (simd4 word_add kq a5))) /\
            word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
            word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
            word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
            word_subword (read YMM6_SSE s) (0,128) = sha256_msg2 a6 a5 /\
            word_subword (read YMM7_SSE s) (0,128) = (mask:int128) /\
            word_subword (read YMM8_SSE s) (0,128) = (mask:int128))
       (MAYCHANGE [RIP] ,,
        MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM6_SSE; YMM7_SSE] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x2ce`
   `\s. read RCX s = kptr /\
        read (memory :> bytes128 (word_add kptr (word 352))) s = kq1 /\
        word_subword (read YMM0_SSE s) (0,128) = simd4 word_add kq a5 /\
        word_subword (read YMM1_SSE s) (0,128) =
          ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
        word_subword (read YMM2_SSE s) (0,128) =
          CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
        word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
        word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
        word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
        word_subword (read YMM6_SSE s) (0,128) = (a6:int128) /\
        word_subword (read YMM8_SSE s) (0,128) = (mask:int128)` THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
    REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC(REWRITE_RULE[SOME_FLAGS]
        SHA256_COMPRESS_HW_GROUP_STEP4_G14_PACKED_PLUS)]);;
Printf.printf "S053_G14_FULL_PLUS hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_GROUP4_FULL_S_G14_PLUS))
  (List.length (frees (concl SHA256_COMPRESS_HW_GROUP4_FULL_S_G14_PLUS)));;
Printf.printf "S053_G14_FULL_PLUS_DONE\n%!";;

(* ========================================================================= *)
(* Session 053 -- CORE_TAIL_TO_2F0_PLUS: the loop-body tail with the byteswap  *)
(* mask threaded (for the multi-block invariant).  Identical to                *)
(* CORE_TAIL_TO_2F0 but the g14 leg is FULL_S_G14_PLUS, and YMM7=mask &         *)
(* YMM8=mask are carried into the POST so the next loop iteration's pshufb has  *)
(* the mask.  YMM8 rides untouched; YMM7 is re-established by g14 then rides     *)
(* g15kload (K-load, YMM7-neutral) to pc+0x2f0.                                 *)
(* ========================================================================= *)
let SHA256_COMPRESS_HW_CORE_TAIL_TO_2F0_PLUS =
  let strip_atom th =
    let bod = snd(strip_forall(concl th)) in
    let ens = if is_imp bod then snd(dest_imp bod) else bod in
    let l,c = dest_comb ens in let l2,q = dest_comb l in let _,p = dest_comb l2 in (p,q,c) in
  let vbyname th n = find (fun v -> name_of v = n) (fst(strip_forall(concl th))) in
  let conjs_of_lam q = let s,body = dest_abs q in s, conjuncts body in
  let contains s sub =
    let ls=String.length s and lsub=String.length sub in
    let rec go i = i+lsub<=ls && (String.sub s i lsub = sub || go(i+1)) in go 0 in
  let is_kread off c =
    is_eq c && contains (string_of_term c) "bytes128"
            && contains (string_of_term c) ("(word " ^ off ^ ")") in
  let kread_for s src_svar src_conjs off =
    vsubst[s,src_svar] (find (is_kread off) src_conjs) in
  let ymm_rhs post nm =
    let _,cs = conjs_of_lam post in
    let hit = find (fun c -> is_eq c && contains (string_of_term(fst(dest_eq c))) nm) cs in
    snd(dest_eq hit) in
  let list_of_abef post =
    let ymm1 = ymm_rhs post "YMM1_SSE" in
    rand(rand(rator(rator(rator ymm1)))) in
  let post_ring q =
    (list_of_abef q, ymm_rhs q "YMM3_SSE", ymm_rhs q "YMM4_SSE",
     ymm_rhs q "YMM5_SSE", ymm_rhs q "YMM6_SSE") in
  let vG13 = SHA256_COMPRESS_HW_GROUP4_FULL_S_G13 in
  let g13th = INST [`kq0:int128`, `kq:int128`; `kq1:int128`, `kq1:int128`]
                   (SPEC_ALL vG13) in
  let (pg13,qg13,cg13) = strip_atom g13th in
  let (l13,a313,a413,a513,a613) = post_ring qg13 in
  (* g14: FULL_S_G14_PLUS (binders kq,kq1,a3..a6,mask). map kq->kq1, kq1->kq2.  *)
  let g14th =
    let base = SPEC_ALL SHA256_COMPRESS_HW_GROUP4_FULL_S_G14_PLUS in
    INST [ `kq1:int128`, vbyname SHA256_COMPRESS_HW_GROUP4_FULL_S_G14_PLUS "kq";
           `kq2:int128`, vbyname SHA256_COMPRESS_HW_GROUP4_FULL_S_G14_PLUS "kq1";
           l13,  vbyname SHA256_COMPRESS_HW_GROUP4_FULL_S_G14_PLUS "l";
           a313, vbyname SHA256_COMPRESS_HW_GROUP4_FULL_S_G14_PLUS "a3";
           a413, vbyname SHA256_COMPRESS_HW_GROUP4_FULL_S_G14_PLUS "a4";
           a513, vbyname SHA256_COMPRESS_HW_GROUP4_FULL_S_G14_PLUS "a5";
           a613, vbyname SHA256_COMPRESS_HW_GROUP4_FULL_S_G14_PLUS "a6" ] base in
  let (pg14,qg14,cg14) = strip_atom g14th in
  let (l14,a314,a414,a514,a614) = post_ring qg14 in
  let g15kth =
    let base = SPEC_ALL SHA256_COMPRESS_HW_GROUP4_G15_KLOAD in
    INST [ `kq2:int128`, vbyname SHA256_COMPRESS_HW_GROUP4_G15_KLOAD "kq";
           l14,  vbyname SHA256_COMPRESS_HW_GROUP4_G15_KLOAD "l";
           a314, vbyname SHA256_COMPRESS_HW_GROUP4_G15_KLOAD "a3";
           a414, vbyname SHA256_COMPRESS_HW_GROUP4_G15_KLOAD "a4";
           a514, vbyname SHA256_COMPRESS_HW_GROUP4_G15_KLOAD "a5";
           a614, vbyname SHA256_COMPRESS_HW_GROUP4_G15_KLOAD "a6" ] base in
  let (pg15,qg15,cg15) = strip_atom g15kth in
  let svar13,pg13c = conjs_of_lam pg13 in
  let sg14,pg14c = conjs_of_lam pg14 in
  let sg15,pg15c = conjs_of_lam pg15 in
  let sv = `s:x86state` in
  let rdx_rider = `read RDX s = (rdxin:int64)` in
  let mask_rider = `word_subword (read YMM8_SSE s) (0,128) = (mask:int128)` in
  let ymm7_post = `word_subword (read YMM7_SSE s) (0,128) = (mask:int128)` in
  let mk_r r s = vsubst[s,sv] r in
  (* frame: same as CORE_TAIL_TO_2F0 (YMM7 in MAYCHANGE, it IS written by g14). *)
  let full_frame =
    `MAYCHANGE [RIP] ,,
     MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM5_SSE; YMM6_SSE; YMM7_SSE] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]` in
  (* PRE = g13 pre-core + K@352 (rides to g14/g15) + RDX + YMM8=mask riders.    *)
  let pre_extra = [ kread_for svar13 sg14 pg14c "352" ] in
  let pre_lam = mk_abs(svar13,
    list_mk_conj (pg13c @ pre_extra @ [mk_r rdx_rider svar13; mk_r mask_rider svar13])) in
  (* POST = g15kload post-core + RDX + YMM7=mask + YMM8=mask.                    *)
  let sg15q,qg15c = conjs_of_lam qg15 in
  let post_lam = mk_abs(sg15q,
    list_mk_conj (qg15c @ [mk_r rdx_rider sg15q; mk_r ymm7_post sg15q; mk_r mask_rider sg15q])) in
  let ens_head = rator(rator(rator(snd(dest_imp(snd(strip_forall(concl vG13))))))) in
  let mk_ensures p q c = mk_comb(mk_comb(mk_comb(ens_head,p),q),c) in
  let bvars = [`pc:num`;`kbase:num`;`kptr:int64`;`l:int32 list`;
               `kq0:int128`;`kq1:int128`;`kq2:int128`;
               `a3:int128`;`a4:int128`;`a5:int128`;`a6:int128`;`rdxin:int64`;`mask:int128`] in
  let hyps = list_mk_conj
    [`aligned 16 (word_add (kptr:int64) (word 288))`;
     `aligned 16 (word_add (kptr:int64) (word 320))`;
     `aligned 16 (word_add (kptr:int64) (word 352))`] in
  let comp_concl = list_mk_forall(bvars, mk_imp(hyps, mk_ensures pre_lam post_lam full_frame)) in
  let seam_core pre =
    let s,cs = conjs_of_lam pre in
    let keep c = not(contains (string_of_term c) "bytes_loaded")
                 && not(contains (string_of_term c) "read RIP") in
    (s, filter keep cs) in
  (* seamQ1 @0x2c2 = g14_PLUS pre-core + RDX + (YMM8=mask already in g14 pre).   *)
  let seamQ1 = let s,cs = seam_core pg14 in mk_abs(s, list_mk_conj (cs @ [mk_r rdx_rider s])) in
  (* seamQ2 @0x2e4 = g15kload pre-core + RDX + YMM7=mask + YMM8=mask riders.     *)
  let seamQ2 = let s,cs = seam_core pg15 in
    mk_abs(s, list_mk_conj (cs @ [mk_r rdx_rider s; mk_r ymm7_post s; mk_r mask_rider s])) in
  prove
   (comp_concl,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[SOME_FLAGS] THEN
    ENSURES_SEQUENCE_TAC `pc + 0x2c2` seamQ1 THEN CONJ_TAC THENL
     [MP_TAC(REWRITE_RULE[SOME_FLAGS] g13th) THEN ASM_REWRITE_TAC[] THEN
      ENSURES_SUBLEMMA_TAC execup "s" "s'" THEN ASM_REWRITE_TAC[];
      ENSURES_SEQUENCE_TAC `pc + 0x2e4` seamQ2 THEN CONJ_TAC THENL
       [MP_TAC(REWRITE_RULE[SOME_FLAGS] g14th) THEN ASM_REWRITE_TAC[] THEN
        (ENSURES_SUBLEMMA_TAC execup "s" "s'" ORELSE
         ENSURES_SUBLEMMA_REFL_TAC execup "s" "s'") THEN ASM_REWRITE_TAC[];
        MP_TAC(REWRITE_RULE[SOME_FLAGS] g15kth) THEN ASM_REWRITE_TAC[] THEN
        (ENSURES_SUBLEMMA_TAC execup "s" "s'" ORELSE
         ENSURES_SUBLEMMA_REFL_TAC execup "s" "s'") THEN ASM_REWRITE_TAC[]]]);;
Printf.printf "S053_CORE_TAIL_TO_2F0_PLUS hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_CORE_TAIL_TO_2F0_PLUS))
  (List.length (frees (concl SHA256_COMPRESS_HW_CORE_TAIL_TO_2F0_PLUS)));;
Printf.printf "S053_CORETAILPLUS_DONE\n%!";;

(* ========================================================================= *)
(* Session 053 -- CORE_38_TO_2F0: the RDX+mask-carrying LOOP BODY, pc+0x38 ->  *)
(* pc+0x2f0 (head-through-tail, state entering in registers).  Adapts the      *)
(* CORE_TO_2F0 composer: head := HEAD38_ABS (pc+0x38->0xf4, abstract state l   *)
(* in YMM1/YMM2), steadies R0..G12 unchanged, tail := CORE_TAIL_TO_2F0_PLUS     *)
(* (threads the byteswap mask).  Riders through every seam: YMM9/YMM10 (the     *)
(* feed-forward init saves), RDX (the loop counter, untouched until the dec),   *)
(* and YMM8 = the concrete byteswap-mask literal (durable, set once by ENTRY).  *)
(* NO RDI rider here (RDI is only touched by the once-only ENTRY load and the   *)
(* EXIT store, both outside pc+0x38..0x2f0).  The composed state list l is      *)
(* abstract (bound by the loop invariant to sha256_hash_blocks m_fn H i).       *)
(* ========================================================================= *)
let masklit = `word 16018520953223639909183530438118932995 : int128`;;

let strip_atom th =
  let bod = snd(strip_forall(concl th)) in
  let ens = if is_imp bod then snd(dest_imp bod) else bod in
  let l,c = dest_comb ens in let l2,q = dest_comb l in let _,p = dest_comb l2 in (p,q,c);;
let ens_of th = let bod = snd(strip_forall(concl th)) in
  if is_imp bod then snd(dest_imp bod) else bod;;
let conjs_of_lam q = let s,body = dest_abs q in s, conjuncts body;;
let contains s sub =
  let ls=String.length s and lsub=String.length sub in
  let rec go i = i+lsub<=ls && (String.sub s i lsub = sub || go(i+1)) in go 0;;
let findc sub cs = find (fun c -> contains (string_of_term c) sub) cs;;
let is_kread off c =
  is_eq c && contains (string_of_term c) "bytes128"
          && contains (string_of_term c) ("(word " ^ off ^ ")");;
let kread_in off cs = find (is_kread off) cs;;
let nred_rule = CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV
                          THENC DEPTH_CONV NUM_SUB_CONV THENC DEPTH_CONV NUM_LE_CONV);;
let keepseam c = not(contains (string_of_term c) "bytes_loaded")
                 && not(contains (string_of_term c) "read RIP");;
let sv = `s:x86state`;;
let rebase lam = let s,cs = conjs_of_lam lam in map (vsubst[sv,s]) cs;;

let stlist = `l:int32 list`;;
let kquad n =
  let el j = list_mk_comb(`EL:num->(int32)list->int32`,
               [mk_small_numeral(4*n+j);`sha256_constants:int32 list`]) in
  list_mk_comb(`WQUAD:int32->int32->int32->int32->int128`,[el 0;el 1;el 2;el 3]);;
let steady_leg th g =
  let sp = SPECL [`pc:num`;`kbase:num`;`kptr:int64`;`m:int32 list`;stlist;
                  mk_small_numeral g] th in
  REWRITE_RULE[] (nred_rule (SPEC (kquad (g+1)) sp));;

let head = INST [kquad 4, `kq4:int128`] (SPEC_ALL SHA256_COMPRESS_HW_HEAD38_ABS);;
let steadies =
 [ (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_R0  4),  4, 0x0f4, 0x120;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_R1  5),  5, 0x120, 0x14d;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_R2  6),  6, 0x14d, 0x17a;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_R3  7),  7, 0x17a, 0x1a7;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_G8  8),  8, 0x1a7, 0x1d7;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_G9  9),  9, 0x1d7, 0x207;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_G10 10), 10, 0x207, 0x237;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_G11 11), 11, 0x237, 0x267;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_G12 12), 12, 0x267, 0x297 ];;

let stlist_cr52 = `sha256_compress_rounds m (l:int32 list) 52 : int32 list`;;
let tail = SPECL [`pc:num`;`kbase:num`;`kptr:int64`; stlist_cr52;
                  kquad 13; `kqA:int128`; `kqB:int128`;
                  `WWIN m 48:int128`;`WWIN m 52:int128`;
                  `PADP m 40:int128`;`MSG1P m 44:int128`;`rdxin:int64`; masklit]
             SHA256_COMPRESS_HW_CORE_TAIL_TO_2F0_PLUS;;

let (pH,qH,fH) = strip_atom head;;
let pHc = rebase pH and qHc = rebase qH;;
let ymm9  = findc "YMM9_SSE" qHc;;
let ymm10 = findc "YMM10_SSE" qHc;;
let rdx_rider0 = `read RDX s = (rdxin:int64)`;;
let ymm8_rider = `word_subword (read YMM8_SSE s) (0,128) =
                  word 16018520953223639909183530438118932995 : int128`;;
let riders = [ymm9; ymm10; rdx_rider0; ymm8_rider];;

let leg_pre th = rebase (let (p,_,_)=strip_atom th in p);;
let leg_th (th,_,_,_) = th;;
let steady_offs = [32;64;96;128;160;192;224;256;288];;
let tail_offs   = [320;352];;
let allwin = steady_offs @ tail_offs;;
let steady_kterm off =
  let k = off/32 in let leg = List.nth steadies (k-1) in
  kread_in (string_of_int off) (leg_pre (leg_th leg));;
let pTc = rebase (let (p,_,_)=strip_atom tail in p);;
let kterm off =
  if off <= 288 then steady_kterm off else kread_in (string_of_int off) pTc;;

let core cs = filter keepseam cs;;
let no_rdx cs = filter (fun c -> not(contains (string_of_term c) "read RDX")) cs;;
let no_riders cs = filter (fun c -> not(contains (string_of_term c) "read RDX")
                       && not(contains (string_of_term c) "YMM8_SSE")) cs;;
let seam_steady (th,g,_,_) =
  let c = 32*(g-4) in
  let carry = map kterm (filter (fun w -> not(w <= c+32)) allwin) in
  mk_abs(sv, list_mk_conj (core (leg_pre th) @ riders @ carry));;
let seam_tail =
  mk_abs(sv, list_mk_conj (no_riders (core pTc) @ riders));;

let (_,qTail,_) = strip_atom tail;;
let qTailc = rebase qTail;;
let post_lam = mk_abs(sv, list_mk_conj (no_riders qTailc @ riders));;

let pre_lam = mk_abs(sv, list_mk_conj (pHc @ map kterm allwin @ [rdx_rider0; ymm8_rider]));;

let ens_head = rator(rator(rator(ens_of head)));;
let mk_ensures p q c = mk_comb(mk_comb(mk_comb(ens_head,p),q),c);;
let comp_frame =
  `MAYCHANGE [RIP; RSI] ,,
   MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM5_SSE;
              YMM6_SSE; YMM7_SSE; YMM9_SSE; YMM10_SSE] ,,
   MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;
let bvars = [`pc:num`;`kbase:num`;`kptr:int64`;`m:int32 list`;`l:int32 list`;
             `mptr:int64`;`kqA:int128`;`kqB:int128`;`rdxin:int64`];;
let comp_hyps = list_mk_conj
 [`aligned 16 (kptr:int64)`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551488))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551520))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551552))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551584))`];;
let comp_concl = list_mk_forall(bvars, mk_imp(comp_hyps, mk_ensures pre_lam post_lam comp_frame));;
Printf.printf "CORE_38_TO_2F0 concl built. frees(concl)=%d\n%!" (List.length(frees comp_concl));;

let pcterm n = mk_comb(mk_comb(`(+):num->num->num`,`pc:num`), mk_small_numeral n);;
let leg_tac th =
  MP_TAC(REWRITE_RULE[SOME_FLAGS] th) THEN ASM_REWRITE_TAC[] THEN
  (ENSURES_SUBLEMMA_TAC execup "s" "s'" ORELSE
   ENSURES_SUBLEMMA_REFL_TAC execup "s" "s'") THEN ASM_REWRITE_TAC[];;
let rec build entries final = match entries with
  | [] -> leg_tac final
  | (off,seam,disch)::rest ->
      ENSURES_SEQUENCE_TAC (pcterm off) seam THEN
      CONJ_TAC THENL [ leg_tac disch; build rest final ];;
let steady_entries =
  let rec go prev = function
    | [] -> []
    | (th,g,e,x)::rest -> (e, seam_steady (th,g,e,x), prev) :: go th rest in
  match steadies with
  | (th0,g0,e0,x0)::rest -> (e0, seam_steady (th0,g0,e0,x0), head) :: go th0 rest
  | [] -> failwith "no steadies";;
let g12th = leg_th (List.nth steadies 8);;
let entries = steady_entries @ [ 0x297, seam_tail, g12th ];;
Printf.printf "entries=%d (expect 10)\n%!" (List.length entries);;

let mk_align_term n =
  vsubst [mk_small_numeral n, `n:num`]
    `aligned 16 (word_add (kptr:int64) (word n))`;;
let mk_align_sub n =
  let t = mk_align_term n in
  SUBGOAL_THEN t ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORMALIZE_ALIGNED_WORD_CONV t]; ALL_TAC];;

let SHA256_COMPRESS_HW_CORE_38_TO_2F0 = prove
 (comp_concl,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  EVERY (map mk_align_sub [32;64;96;128;160;192;224;256;288;320;352]) THEN
  build entries tail);;
Printf.printf "S053_CORE_38_TO_2F0 hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_CORE_38_TO_2F0))
  (List.length(frees(concl SHA256_COMPRESS_HW_CORE_38_TO_2F0)));;
Printf.printf "S053_CORE_38_TO_2F0_DONE\n%!";;

(* ========================================================================= *)
(* Session 053 -- CORE_LOOP_BODY: one full loop iteration pc+0x38 -> pc+0x30c  *)
(* (the back-edge jne).  Chains CORE_38_TO_2F0(rdxin) ; G15_RAW_PLUS ;          *)
(* FEEDFWD_PLUS.  RDX generic (rdxin), ZF exposed in the POST                   *)
(* (read ZF s <=> val (word_sub rdxin (word 1)) = 0), the running state         *)
(* advanced to YMM1/YMM2 = simd4_add (raw g15 crypto)(initabef/initcdgh) where   *)
(* init = the YMM9/YMM10 feed-forward saves (= ABEF/CDGH_PACK of the ENTRY state *)
(* l).  Crypto kept RAW here; the spec fold to sha256_block is CORE_LOOP_BODY_   *)
(* SPEC below.  The byteswap mask YMM7=YMM8=masklit rides through G15/FEEDFWD     *)
(* (neither touches YMM7/YMM8), so it is available for the next iteration.       *)
(* YMM9/YMM10 ride seamA (G15 leaves them; not in its frame) into FEEDFWD's PRE. *)
(* ========================================================================= *)
let masklit = `word 16018520953223639909183530438118932995 : int128`;;
let strip_atom th =
  let bod = snd(strip_forall(concl th)) in
  let ens = if is_imp bod then snd(dest_imp bod) else bod in
  let l,c = dest_comb ens in let l2,q = dest_comb l in let _,p = dest_comb l2 in (p,q,c);;
let ens_of th = let bod = snd(strip_forall(concl th)) in
  if is_imp bod then snd(dest_imp bod) else bod;;
let conjs_of_lam q = let s,body = dest_abs q in s, conjuncts body;;
let contains s sub =
  let ls=String.length s and lsub=String.length sub in
  let rec go i = i+lsub<=ls && (String.sub s i lsub = sub || go(i+1)) in go 0;;
let findc sub cs = find (fun c -> contains (string_of_term c) sub) cs;;
let sv = `s:x86state`;;
let rebase lam = let s,cs = conjs_of_lam lam in map (vsubst[sv,s]) cs;;
let ymm_rhs cs nm = snd(dest_eq(findc nm cs));;

let core38 = SPEC_ALL SHA256_COMPRESS_HW_CORE_38_TO_2F0;;
let (pc0,qc0,fc0) = strip_atom core38;;
let qc0c = rebase qc0;;
let wk_t   = ymm_rhs qc0c "YMM0_SSE";;
let abef_t = ymm_rhs qc0c "YMM1_SSE";;
let cdgh_t = ymm_rhs qc0c "YMM2_SSE";;
let a3_t   = ymm_rhs qc0c "YMM3_SSE";;
let a4_t   = ymm_rhs qc0c "YMM4_SSE";;
let a5_t   = ymm_rhs qc0c "YMM5_SSE";;
let a6_t   = ymm_rhs qc0c "YMM6_SSE";;
let ia_t   = ymm_rhs qc0c "YMM9_SSE";;
let ic_t   = ymm_rhs qc0c "YMM10_SSE";;
let kq352_t = snd(dest_eq(find (fun c -> contains (string_of_term c) "(word 352)")
                            (filter is_eq qc0c)));;

let g15p = SPECL [`pc:num`;`kbase:num`;`kptr:int64`;
                  `word_add kptr (word 352):int64`; kq352_t;
                  wk_t; abef_t; cdgh_t; a3_t; a4_t; a5_t; a6_t; `rdxin:int64`]
             SHA256_COMPRESS_HW_GROUP_STEP4_G15_RAW_PLUS;;
let (pg,qg,fg) = strip_atom g15p;;
let qgc = rebase qg;;
let g15_abef = ymm_rhs qgc "YMM1_SSE";;
let g15_cdgh = ymm_rhs qgc "YMM2_SSE";;

let ffp = SPECL [`pc:num`;`kbase:num`; g15_abef; g15_cdgh; ia_t; ic_t;
                 `word_sub rdxin (word 1):int64`;
                 `val (word_sub rdxin (word 1):int64) = 0`]
            SHA256_COMPRESS_HW_FEEDFWD_PLUS;;
let (pf,qf,ff) = strip_atom ffp;;
let qfc = rebase qf;;

let pre_lam = pc0;;
let post_lam = qf;;
let keepseam c = not(contains (string_of_term c) "bytes_loaded")
                 && not(contains (string_of_term c) "read RIP");;
let core cs = filter keepseam cs;;
let ens_head = rator(rator(rator(ens_of core38)));;
let mk_ensures p q c = mk_comb(mk_comb(mk_comb(ens_head,p),q),c);;
let comp_frame =
  `MAYCHANGE [RIP; RSI; RDX] ,,
   MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM5_SSE;
              YMM6_SSE; YMM7_SSE; YMM9_SSE; YMM10_SSE] ,,
   MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;
let bvars = [`pc:num`;`kbase:num`;`kptr:int64`;`m:int32 list`;`l:int32 list`;
             `mptr:int64`;`kqA:int128`;`kqB:int128`;`rdxin:int64`];;
let comp_hyps = list_mk_conj
 [`aligned 16 (kptr:int64)`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551488))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551520))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551552))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551584))`];;
let comp_concl = list_mk_forall(bvars, mk_imp(comp_hyps, mk_ensures pre_lam post_lam comp_frame));;
Printf.printf "CORE_LOOP_BODY concl built. frees=%d\n%!" (List.length(frees comp_concl));;

(* seamA @0x2f0 = G15 PRE-core + mask(YMM7/8) + init(YMM9/10) riders (all ride  *)
(* CORE_38->G15).  seamB @0x302 = FEEDFWD PRE-core (already has YMM9/10) + mask. *)
let ymm9_r  = subst [ia_t,`initabef0:int128`]
   `word_subword (read YMM9_SSE s) (0,128) = (initabef0:int128)`;;
let ymm10_r = subst [ic_t,`initcdgh0:int128`]
   `word_subword (read YMM10_SSE s) (0,128) = (initcdgh0:int128)`;;
let mask7 = `word_subword (read YMM7_SSE s) (0,128) =
             word 16018520953223639909183530438118932995 : int128`;;
let mask8 = `word_subword (read YMM8_SSE s) (0,128) =
             word 16018520953223639909183530438118932995 : int128`;;
let seamA = mk_abs(sv, list_mk_conj (core (rebase pg) @ [mask7; mask8; ymm9_r; ymm10_r]));;
let seamB = mk_abs(sv, list_mk_conj (core (rebase pf) @ [mask7; mask8]));;

let pcterm n = mk_comb(mk_comb(`(+):num->num->num`,`pc:num`), mk_small_numeral n);;
let leg_tac th =
  MP_TAC(REWRITE_RULE[SOME_FLAGS] th) THEN ASM_REWRITE_TAC[] THEN
  (ENSURES_SUBLEMMA_TAC execup "s" "s'" ORELSE
   ENSURES_SUBLEMMA_REFL_TAC execup "s" "s'") THEN ASM_REWRITE_TAC[];;

let SHA256_COMPRESS_HW_CORE_LOOP_BODY = prove
 (comp_concl,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC (pcterm 0x2f0) seamA THEN CONJ_TAC THENL
   [leg_tac core38;
    ENSURES_SEQUENCE_TAC (pcterm 0x302) seamB THEN CONJ_TAC THENL
     [leg_tac g15p;
      leg_tac ffp]]);;
Printf.printf "S053_CORE_LOOP_BODY hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_CORE_LOOP_BODY))
  (List.length(frees(concl SHA256_COMPRESS_HW_CORE_LOOP_BODY)));;
Printf.printf "S053_CORE_LOOP_BODY_DONE\n%!";;

(* ========================================================================= *)
(* Session 053 -- CORE_LOOP_BODY_SPEC: the SPEC-form loop iteration.          *)
(* Folds CORE_LOOP_BODY's raw-crypto POST (YMM1/2 = simd4_add(raw g15 rnds2    *)
(* feed-forward)(YMM9/10 init saves)) to the FIPS per-block form:              *)
(*   YMM1 = ABEF_PACK (EL 0/1/4/5 (sha256_block m l))                          *)
(*   YMM2 = CDGH_PACK (EL 2/3/6/7 (sha256_block m l))                          *)
(* i.e. one loop iteration maps the running state l -> sha256_block (m l).     *)
(* Recipe = CORE_BODY_SPEC's (kqA/kqB := WQUAD(EL 56..59/60..63 consts);        *)
(* wring40/padp44/wring44; cr52/56/60; g15 GROUP_ADVANCE GA1;GA2 + ATCF;        *)
(* GSYM CR4; SIMD4_ADD_ABEF/CDGH; GSYM BLOCK_ELS) but over the ABSTRACT state   *)
(* list l -- so BLOCK_ELS is regeneralized to l (BLOCK_ELS_L below).  The init  *)
(* YMM9/YMM10 = ABEF/CDGH_PACK(EL.. l) is the feed-forward H_in; simd4_add of   *)
(* the cr64 crypto packs + the H_in packs = the packed sha256_block.  This is   *)
(* the loud-failure K-map test for the loop body (PASSED: concl has            *)
(* sha256_block x8, sha256_rnds2 x0).                                          *)
(* ========================================================================= *)
let BLOCK_ELS_L =
  CONV_RULE(DEPTH_CONV EL_CONV) (prove
   (list_mk_conj (map (fun i ->
       let eli lst = list_mk_comb(`EL:num->(int32)list->int32`,[mk_small_numeral i; lst]) in
       mk_eq(eli (list_mk_comb(`sha256_block`,[`m:int32 list`; `l:int32 list`])),
             list_mk_comb(`word_add:int32->int32->int32`,
               [eli (list_mk_comb(`sha256_compress_rounds`,[`m:int32 list`;`l:int32 list`;`64`]));
                eli `l:int32 list`])))
       [0;1;2;3;4;5;6;7]),
    REWRITE_TAC[sha256_block] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]));;

let SHA256_COMPRESS_HW_CORE_LOOP_BODY_SPEC =
  let kqA_val = `WQUAD (EL 56 sha256_constants) (EL 57 sha256_constants)
                       (EL 58 sha256_constants) (EL 59 sha256_constants) : int128` in
  let kqB_val = `WQUAD (EL 60 sha256_constants) (EL 61 sha256_constants)
                       (EL 62 sha256_constants) (EL 63 sha256_constants) : int128` in
  let body' = INST [kqA_val, `kqA:int128`; kqB_val, `kqB:int128`]
                (SPEC_ALL SHA256_COMPRESS_HW_CORE_LOOP_BODY) in
  let nred_cr  = CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV) in
  let nred_off = CONV_RULE(DEPTH_CONV NUM_ADD_CONV) in
  let cr_step g = nred_cr (SPECL [`m:int32 list`; `l:int32 list`; mk_small_numeral g]
                            CR4_SPEC_STEP_WWIN) in
  let cr52 = cr_step 13 and cr56 = cr_step 14 and cr60 = cr_step 15 in
  let wring40 = nred_off (SPECL [`m:int32 list`; `40`] WRING_WWIN) in
  let wring44 = nred_off (SPECL [`m:int32 list`; `44`] WRING_WWIN) in
  let padp44  = GSYM(nred_off (SPECL [`m:int32 list`; `44`] PADP)) in
  let stepA = REWRITE_RULE[wring40; padp44; wring44; cr52; cr56] body' in
  let l60 = `sha256_compress_rounds m (l:int32 list) 60 : int32 list` in
  let wk15 = `simd4 word_add
     (WQUAD (EL 60 sha256_constants) (EL 61 sha256_constants)
            (EL 62 sha256_constants) (EL 63 sha256_constants))
     (WWIN m 60) : int128` in
  let GA = CONV_RULE(TOP_DEPTH_CONV let_CONV)
             (SPECL [l60; wk15] SHA256_RNDS2_GROUP_ADVANCE) in
  let GA1 = CONJUNCT1 GA and GA2 = CONJUNCT2 GA in
  let ATCF = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [l60;
             `word_subword (wk15v:int128) (0,32):int32`; `word_subword (wk15v:int128) (32,32):int32`;
             `word_subword (wk15v:int128) (64,32):int32`; `word_subword (wk15v:int128) (96,32):int32`]
            ABEF_TWO_IS_CDGH_FOUR) in
  let ATCF = INST [wk15, `wk15v:int128`] ATCF in
  let stepB0 = REWRITE_RULE[GA1] stepA in
  let stepB1 = REWRITE_RULE[GA2] stepB0 in
  let stepB  = REWRITE_RULE[ATCF] stepB1 in
  let stepC = REWRITE_RULE[cr60] (REWRITE_RULE[GSYM CR4] stepB) in
  let step2 = REWRITE_RULE[SIMD4_ADD_ABEF; SIMD4_ADD_CDGH] stepC in
  let step3 = REWRITE_RULE[GSYM BLOCK_ELS_L] step2 in
  GEN_ALL step3;;
Printf.printf "S053_CORE_LOOP_BODY_SPEC hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_CORE_LOOP_BODY_SPEC))
  (List.length(frees(concl SHA256_COMPRESS_HW_CORE_LOOP_BODY_SPEC)));;
Printf.printf "S053_CORE_LOOP_BODY_SPEC_DONE\n%!";;

(* ========================================================================= *)
(* Session 054 -- Strengthened loop body (_PLUS lemmas): thread RSI=mptr+64   *)
(* and YMM7=mask into the per-iteration POST.  CORE_LOOP_BODY_SPEC's POST is   *)
(* minimal (RIP/RDX/ZF/YMM1/YMM2); the multi-block loop invariant additionally *)
(* needs RSI (=dptr+64i) and YMM7 (=mask).  These are the ONLY two facts the    *)
(* invariant needs that ride the frame yet are dropped from the POST (RCX,      *)
(* YMM8, K-memory and message-memory are NOT in the frame, so they ride and are *)
(* re-asserted freely).  RSI is set once by HEAD38's lea and untouched after,   *)
(* so it threads as a pure rider like YMM8; YMM7 is re-established by g14 and    *)
(* carried through CORE_38's POST + the seams, just dropped from post_lam.       *)
(* CORE_38_TO_2F0_PLUS = the s053 CORE_38_TO_2F0 with RSI added to the riders;   *)
(* CORE_LOOP_BODY_PLUS = compose ; G15_RAW_PLUS ; FEEDFWD_PLUS with RSI/YMM7 in  *)
(* the seams+post; CORE_LOOP_BODY_SPEC_PLUS = the identical fold recipe.         *)
(* ========================================================================= *)
(* --- generic helpers (re-declared locally to be safe) --- *)
let sv = `s:x86state`;;
let contains s sub =
  let ls=String.length s and lsub=String.length sub in
  let rec go i = i+lsub<=ls && (String.sub s i lsub = sub || go(i+1)) in go 0;;
let strip_atom th =
  let bod = snd(strip_forall(concl th)) in
  let ens = if is_imp bod then snd(dest_imp bod) else bod in
  let l,c = dest_comb ens in let l2,q = dest_comb l in let _,p = dest_comb l2 in (p,q,c);;
let ens_of th = let bod = snd(strip_forall(concl th)) in
  if is_imp bod then snd(dest_imp bod) else bod;;
let conjs_of_lam q = let s,body = dest_abs q in s, conjuncts body;;
let findc sub cs = find (fun c -> contains (string_of_term c) sub) cs;;
let rebase lam = let s,cs = conjs_of_lam lam in map (vsubst[sv,s]) cs;;
let keepseam c = not(contains (string_of_term c) "bytes_loaded")
                 && not(contains (string_of_term c) "read RIP");;
let core cs = filter keepseam cs;;
let is_kread off c =
  is_eq c && contains (string_of_term c) "bytes128"
          && contains (string_of_term c) ("(word " ^ off ^ ")");;
let kread_in off cs = find (is_kread off) cs;;
let nred_rule = CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV
                          THENC DEPTH_CONV NUM_SUB_CONV THENC DEPTH_CONV NUM_LE_CONV);;
let pcterm n = mk_comb(mk_comb(`(+):num->num->num`,`pc:num`), mk_small_numeral n);;
let masklit = `word 16018520953223639909183530438118932995 : int128`;;

(* --- rebuild CORE_38_TO_2F0 pieces with RSI as an extra rider --- *)
let stlist = `l:int32 list`;;
let kquad n =
  let el j = list_mk_comb(`EL:num->(int32)list->int32`,
               [mk_small_numeral(4*n+j);`sha256_constants:int32 list`]) in
  list_mk_comb(`WQUAD:int32->int32->int32->int32->int128`,[el 0;el 1;el 2;el 3]);;
let steady_leg th g =
  let sp = SPECL [`pc:num`;`kbase:num`;`kptr:int64`;`m:int32 list`;stlist;
                  mk_small_numeral g] th in
  REWRITE_RULE[] (nred_rule (SPEC (kquad (g+1)) sp));;
let head = INST [kquad 4, `kq4:int128`] (SPEC_ALL SHA256_COMPRESS_HW_HEAD38_ABS);;
let steadies =
 [ (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_R0  4),  4, 0x0f4, 0x120;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_R1  5),  5, 0x120, 0x14d;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_R2  6),  6, 0x14d, 0x17a;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_R3  7),  7, 0x17a, 0x1a7;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_G8  8),  8, 0x1a7, 0x1d7;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_G9  9),  9, 0x1d7, 0x207;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_G10 10), 10, 0x207, 0x237;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_G11 11), 11, 0x237, 0x267;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_G12 12), 12, 0x267, 0x297 ];;
let stlist_cr52 = `sha256_compress_rounds m (l:int32 list) 52 : int32 list`;;
let tail = SPECL [`pc:num`;`kbase:num`;`kptr:int64`; stlist_cr52;
                  kquad 13; `kqA:int128`; `kqB:int128`;
                  `WWIN m 48:int128`;`WWIN m 52:int128`;
                  `PADP m 40:int128`;`MSG1P m 44:int128`;`rdxin:int64`; masklit]
             SHA256_COMPRESS_HW_CORE_TAIL_TO_2F0_PLUS;;
let (pH,qH,fH) = strip_atom head;;
let pHc = rebase pH and qHc = rebase qH;;
let ymm9  = findc "YMM9_SSE" qHc;;
let ymm10 = findc "YMM10_SSE" qHc;;
let rsi_rider = `read RSI s = word_add mptr (word 64)`;;   (* NEW rider *)
let rdx_rider0 = `read RDX s = (rdxin:int64)`;;
let ymm8_rider = `word_subword (read YMM8_SSE s) (0,128) =
                  word 16018520953223639909183530438118932995 : int128`;;
let riders = [ymm9; ymm10; rdx_rider0; ymm8_rider; rsi_rider];;  (* + RSI *)
let leg_pre th = rebase (let (p,_,_)=strip_atom th in p);;
let leg_th (th,_,_,_) = th;;
let steady_offs = [32;64;96;128;160;192;224;256;288];;
let tail_offs   = [320;352];;
let allwin = steady_offs @ tail_offs;;
let steady_kterm off =
  let k = off/32 in let leg = List.nth steadies (k-1) in
  kread_in (string_of_int off) (leg_pre (leg_th leg));;
let pTc = rebase (let (p,_,_)=strip_atom tail in p);;
let kterm off =
  if off <= 288 then steady_kterm off else kread_in (string_of_int off) pTc;;
let no_riders cs = filter (fun c -> not(contains (string_of_term c) "read RDX")
                       && not(contains (string_of_term c) "YMM8_SSE")
                       && not(contains (string_of_term c) "read RSI")) cs;;
let seam_steady (th,g,_,_) =
  let c = 32*(g-4) in
  let carry = map kterm (filter (fun w -> not(w <= c+32)) allwin) in
  mk_abs(sv, list_mk_conj (core (leg_pre th) @ riders @ carry));;
let seam_tail =
  mk_abs(sv, list_mk_conj (no_riders (core pTc) @ riders));;
let (_,qTail,_) = strip_atom tail;;
let qTailc = rebase qTail;;
let post_lam = mk_abs(sv, list_mk_conj (no_riders qTailc @ riders));;
let pre_lam = mk_abs(sv, list_mk_conj (pHc @ map kterm allwin @ [rdx_rider0; ymm8_rider]));;
let ens_head = rator(rator(rator(ens_of head)));;
let mk_ensures p q c = mk_comb(mk_comb(mk_comb(ens_head,p),q),c);;
let comp_frame =
  `MAYCHANGE [RIP; RSI] ,,
   MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM5_SSE;
              YMM6_SSE; YMM7_SSE; YMM9_SSE; YMM10_SSE] ,,
   MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;
let bvars = [`pc:num`;`kbase:num`;`kptr:int64`;`m:int32 list`;`l:int32 list`;
             `mptr:int64`;`kqA:int128`;`kqB:int128`;`rdxin:int64`];;
let comp_hyps = list_mk_conj
 [`aligned 16 (kptr:int64)`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551488))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551520))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551552))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551584))`];;
let comp_concl = list_mk_forall(bvars, mk_imp(comp_hyps, mk_ensures pre_lam post_lam comp_frame));;
Printf.printf "CORE_38_TO_2F0_PLUS concl built. frees(concl)=%d\n%!" (List.length(frees comp_concl));;

(* execup is already bound by the loaded file (line 2302); reuse it. *)
let leg_tac th =
  MP_TAC(REWRITE_RULE[SOME_FLAGS] th) THEN ASM_REWRITE_TAC[] THEN
  (ENSURES_SUBLEMMA_TAC execup "s" "s'" ORELSE
   ENSURES_SUBLEMMA_REFL_TAC execup "s" "s'") THEN ASM_REWRITE_TAC[];;
let rec build entries final = match entries with
  | [] -> leg_tac final
  | (off,seam,disch)::rest ->
      ENSURES_SEQUENCE_TAC (pcterm off) seam THEN
      CONJ_TAC THENL [ leg_tac disch; build rest final ];;
let steady_entries =
  let rec go prev = function
    | [] -> []
    | (th,g,e,x)::rest -> (e, seam_steady (th,g,e,x), prev) :: go th rest in
  match steadies with
  | (th0,g0,e0,x0)::rest -> (e0, seam_steady (th0,g0,e0,x0), head) :: go th0 rest
  | [] -> failwith "no steadies";;
let g12th = leg_th (List.nth steadies 8);;
let entries = steady_entries @ [ 0x297, seam_tail, g12th ];;
let mk_align_term n =
  vsubst [mk_small_numeral n, `n:num`]
    `aligned 16 (word_add (kptr:int64) (word n))`;;
let mk_align_sub n =
  let t = mk_align_term n in
  SUBGOAL_THEN t ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORMALIZE_ALIGNED_WORD_CONV t]; ALL_TAC];;

let SHA256_COMPRESS_HW_CORE_38_TO_2F0_PLUS = prove
 (comp_concl,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  EVERY (map mk_align_sub [32;64;96;128;160;192;224;256;288;320;352]) THEN
  build entries tail);;
Printf.printf "S054_CORE_38_TO_2F0_PLUS hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_CORE_38_TO_2F0_PLUS))
  (List.length(frees(concl SHA256_COMPRESS_HW_CORE_38_TO_2F0_PLUS)));;
Printf.printf "S054_CORE_38_TO_2F0_PLUS_DONE\n%!";;

(* ========================================================================= *)
(* CORE_LOOP_BODY_PLUS: compose CORE_38_TO_2F0_PLUS ; G15_RAW_PLUS ;          *)
(* FEEDFWD_PLUS, threading RSI (rides G15/FF frames) and YMM7=mask (rides too) *)
(* into the final POST.  Mirrors the s053 CORE_LOOP_BODY block but with the    *)
(* PLUS core38 and RSI/YMM7 added to seams+post.                               *)
(* ========================================================================= *)
let ymm_rhs cs nm = snd(dest_eq(findc nm cs));;
let core38 = SPEC_ALL SHA256_COMPRESS_HW_CORE_38_TO_2F0_PLUS;;
let (pc0,qc0,fc0) = strip_atom core38;;
let qc0c = rebase qc0;;
let wk_t   = ymm_rhs qc0c "YMM0_SSE";;
let abef_t = ymm_rhs qc0c "YMM1_SSE";;
let cdgh_t = ymm_rhs qc0c "YMM2_SSE";;
let a3_t   = ymm_rhs qc0c "YMM3_SSE";;
let a4_t   = ymm_rhs qc0c "YMM4_SSE";;
let a5_t   = ymm_rhs qc0c "YMM5_SSE";;
let a6_t   = ymm_rhs qc0c "YMM6_SSE";;
let ia_t   = ymm_rhs qc0c "YMM9_SSE";;
let ic_t   = ymm_rhs qc0c "YMM10_SSE";;
let kq352_t = snd(dest_eq(find (fun c -> contains (string_of_term c) "(word 352)")
                            (filter is_eq qc0c)));;
let g15p = SPECL [`pc:num`;`kbase:num`;`kptr:int64`;
                  `word_add kptr (word 352):int64`; kq352_t;
                  wk_t; abef_t; cdgh_t; a3_t; a4_t; a5_t; a6_t; `rdxin:int64`]
             SHA256_COMPRESS_HW_GROUP_STEP4_G15_RAW_PLUS;;
let (pg,qg,fg) = strip_atom g15p;;
let qgc = rebase qg;;
let g15_abef = ymm_rhs qgc "YMM1_SSE";;
let g15_cdgh = ymm_rhs qgc "YMM2_SSE";;
let ffp = SPECL [`pc:num`;`kbase:num`; g15_abef; g15_cdgh; ia_t; ic_t;
                 `word_sub rdxin (word 1):int64`;
                 `val (word_sub rdxin (word 1):int64) = 0`]
            SHA256_COMPRESS_HW_FEEDFWD_PLUS;;
let (pf,qf,ff) = strip_atom ffp;;
let qfc = rebase qf;;

let pre_lam = pc0;;
(* POST = FEEDFWD post-core + RSI=mptr+64 + YMM7=mask (both ride G15/FF). *)
let rsi_post = `read RSI s = word_add mptr (word 64)`;;
let mask7 = `word_subword (read YMM7_SSE s) (0,128) =
             word 16018520953223639909183530438118932995 : int128`;;
let mask8 = `word_subword (read YMM8_SSE s) (0,128) =
             word 16018520953223639909183530438118932995 : int128`;;
let post_lam = mk_abs(sv, list_mk_conj (core qfc @ [rsi_post; mask7; mask8]));;

let ens_head2 = rator(rator(rator(ens_of core38)));;
let mk_ensures2 p q c = mk_comb(mk_comb(mk_comb(ens_head2,p),q),c);;
let comp_frame2 =
  `MAYCHANGE [RIP; RSI; RDX] ,,
   MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM5_SSE;
              YMM6_SSE; YMM7_SSE; YMM9_SSE; YMM10_SSE] ,,
   MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;
let comp_concl2 = list_mk_forall(bvars, mk_imp(comp_hyps, mk_ensures2 pre_lam post_lam comp_frame2));;
Printf.printf "CORE_LOOP_BODY_PLUS concl built. frees=%d\n%!" (List.length(frees comp_concl2));;

(* seamA @0x2f0 = G15 PRE-core + mask(7/8) + init(9/10) + RSI riders.          *)
let ymm9_r  = subst [ia_t,`initabef0:int128`]
   `word_subword (read YMM9_SSE s) (0,128) = (initabef0:int128)`;;
let ymm10_r = subst [ic_t,`initcdgh0:int128`]
   `word_subword (read YMM10_SSE s) (0,128) = (initcdgh0:int128)`;;
let seamA = mk_abs(sv, list_mk_conj (core (rebase pg) @ [mask7; mask8; ymm9_r; ymm10_r; rsi_post]));;
let seamB = mk_abs(sv, list_mk_conj (core (rebase pf) @ [mask7; mask8; rsi_post]));;

let SHA256_COMPRESS_HW_CORE_LOOP_BODY_PLUS = prove
 (comp_concl2,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC (pcterm 0x2f0) seamA THEN CONJ_TAC THENL
   [leg_tac core38;
    ENSURES_SEQUENCE_TAC (pcterm 0x302) seamB THEN CONJ_TAC THENL
     [leg_tac g15p;
      leg_tac ffp]]);;
Printf.printf "S054_CORE_LOOP_BODY_PLUS hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_CORE_LOOP_BODY_PLUS))
  (List.length(frees(concl SHA256_COMPRESS_HW_CORE_LOOP_BODY_PLUS)));;
Printf.printf "S054_CORE_LOOP_BODY_PLUS_DONE\n%!";;

(* ========================================================================= *)
(* CORE_LOOP_BODY_SPEC_PLUS: fold CLB_PLUS crypto to the FIPS sha256_block    *)
(* form (exact s053 recipe, lines 8422-8458), leaving RSI/YMM7/YMM8/RDX/ZF    *)
(* conjuncts untouched.  This is the strengthened per-iteration step function. *)
(* ========================================================================= *)
let SHA256_COMPRESS_HW_CORE_LOOP_BODY_SPEC_PLUS =
  let kqA_val = `WQUAD (EL 56 sha256_constants) (EL 57 sha256_constants)
                       (EL 58 sha256_constants) (EL 59 sha256_constants) : int128` in
  let kqB_val = `WQUAD (EL 60 sha256_constants) (EL 61 sha256_constants)
                       (EL 62 sha256_constants) (EL 63 sha256_constants) : int128` in
  let body' = INST [kqA_val, `kqA:int128`; kqB_val, `kqB:int128`]
                (SPEC_ALL SHA256_COMPRESS_HW_CORE_LOOP_BODY_PLUS) in
  let nred_cr  = CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV) in
  let nred_off = CONV_RULE(DEPTH_CONV NUM_ADD_CONV) in
  let cr_step g = nred_cr (SPECL [`m:int32 list`; `l:int32 list`; mk_small_numeral g]
                            CR4_SPEC_STEP_WWIN) in
  let cr52 = cr_step 13 and cr56 = cr_step 14 and cr60 = cr_step 15 in
  let wring40 = nred_off (SPECL [`m:int32 list`; `40`] WRING_WWIN) in
  let wring44 = nred_off (SPECL [`m:int32 list`; `44`] WRING_WWIN) in
  let padp44  = GSYM(nred_off (SPECL [`m:int32 list`; `44`] PADP)) in
  let stepA = REWRITE_RULE[wring40; padp44; wring44; cr52; cr56] body' in
  let l60 = `sha256_compress_rounds m (l:int32 list) 60 : int32 list` in
  let wk15 = `simd4 word_add
     (WQUAD (EL 60 sha256_constants) (EL 61 sha256_constants)
            (EL 62 sha256_constants) (EL 63 sha256_constants))
     (WWIN m 60) : int128` in
  let GA = CONV_RULE(TOP_DEPTH_CONV let_CONV)
             (SPECL [l60; wk15] SHA256_RNDS2_GROUP_ADVANCE) in
  let GA1 = CONJUNCT1 GA and GA2 = CONJUNCT2 GA in
  let ATCF = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [l60;
             `word_subword (wk15v:int128) (0,32):int32`; `word_subword (wk15v:int128) (32,32):int32`;
             `word_subword (wk15v:int128) (64,32):int32`; `word_subword (wk15v:int128) (96,32):int32`]
            ABEF_TWO_IS_CDGH_FOUR) in
  let ATCF = INST [wk15, `wk15v:int128`] ATCF in
  let stepB0 = REWRITE_RULE[GA1] stepA in
  let stepB1 = REWRITE_RULE[GA2] stepB0 in
  let stepB  = REWRITE_RULE[ATCF] stepB1 in
  let stepC = REWRITE_RULE[cr60] (REWRITE_RULE[GSYM CR4] stepB) in
  let step2 = REWRITE_RULE[SIMD4_ADD_ABEF; SIMD4_ADD_CDGH] stepC in
  let step3 = REWRITE_RULE[GSYM BLOCK_ELS_L] step2 in
  GEN_ALL step3;;
Printf.printf "S054_CORE_LOOP_BODY_SPEC_PLUS hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_CORE_LOOP_BODY_SPEC_PLUS))
  (List.length(frees(concl SHA256_COMPRESS_HW_CORE_LOOP_BODY_SPEC_PLUS)));;
(* K-map sanity: POST must have sha256_block x8, sha256_rnds2 x0. *)
let cc = string_of_term(concl SHA256_COMPRESS_HW_CORE_LOOP_BODY_SPEC_PLUS);;
let count sub =
  let ls=String.length cc and lsub=String.length sub in
  let rec go i n = if i+lsub>ls then n
    else go (i+1) (if String.sub cc i lsub=sub then n+1 else n) in go 0 0;;
Printf.printf "S054_KMAP block=%d rnds2=%d RSI=%d YMM7=%d\n%!"
  (count "sha256_block") (count "sha256_rnds2") (count "read RSI") (count "YMM7_SSE");;
Printf.printf "S054_CORE_LOOP_BODY_SPEC_PLUS_DONE\n%!";;

(* ========================================================================= *)
(* Session 055 -- RIP-carrying body-lemma variants + arithmetic bridges for   *)
(* the CORE_CORRECT body leg.                                                 *)
(*                                                                            *)
(* CLB_SPEC_PLUS's POST does NOT state read RIP (the seam `core` filter strips *)
(* it) while its frame has MAYCHANGE [RIP] -- so composing with the back-edge  *)
(* JNE_BR at pc+0x30c (which needs RIP=pc+0x30c at the seam) is impossible      *)
(* from CLB_SPEC_PLUS as committed.  FEEDFWD_PLUS (the last sub-leg) DOES carry *)
(* read RIP = word(pc+0x30c) in its POST, so we rebuild the body lemma with the *)
(* RIP conjunct re-added to post_lam; the fold recipe (crypto REWRITE_RULEs)    *)
(* passes the RIP conjunct through untouched.  The CLB_PLUS-block file-scope     *)
(* bindings (core38/g15p/ffp/pre_lam/seamA/seamB/comp_frame2/comp_hyps/bvars/    *)
(* ens_head2/mk_ensures2/leg_tac/pcterm/post_lam) are all live here.            *)
(* ========================================================================= *)

(* RIP conjunct at the FEEDFWD exit (pc+0x30c = pc+780). *)
let rip_post = `read RIP s = word (pc + 0x30c)`;;
let post_lam_rip =
  let v, body = dest_abs post_lam in
  mk_abs(v, list_mk_conj (rip_post :: conjuncts body));;
let comp_concl2_rip =
  list_mk_forall(bvars, mk_imp(comp_hyps, mk_ensures2 pre_lam post_lam_rip comp_frame2));;

let SHA256_COMPRESS_HW_CORE_LOOP_BODY_PLUS_RIP = prove
 (comp_concl2_rip,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC (pcterm 0x2f0) seamA THEN CONJ_TAC THENL
   [leg_tac core38;
    ENSURES_SEQUENCE_TAC (pcterm 0x302) seamB THEN CONJ_TAC THENL
     [leg_tac g15p;
      leg_tac ffp]]);;
Printf.printf "S055_CLB_PLUS_RIP hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_CORE_LOOP_BODY_PLUS_RIP))
  (List.length(frees(concl SHA256_COMPRESS_HW_CORE_LOOP_BODY_PLUS_RIP)));;

(* CLB_SPEC_PLUS_RIP: the CLB_SPEC_PLUS crypto fold applied to CLB_PLUS_RIP.    *)
(* Identical recipe (lines 8700-8736); the RIP conjunct is inert under it.      *)
let SHA256_COMPRESS_HW_CORE_LOOP_BODY_SPEC_PLUS_RIP =
  let kqA_val = `WQUAD (EL 56 sha256_constants) (EL 57 sha256_constants)
                       (EL 58 sha256_constants) (EL 59 sha256_constants) : int128` in
  let kqB_val = `WQUAD (EL 60 sha256_constants) (EL 61 sha256_constants)
                       (EL 62 sha256_constants) (EL 63 sha256_constants) : int128` in
  let body' = INST [kqA_val, `kqA:int128`; kqB_val, `kqB:int128`]
                (SPEC_ALL SHA256_COMPRESS_HW_CORE_LOOP_BODY_PLUS_RIP) in
  let nred_cr  = CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV) in
  let nred_off = CONV_RULE(DEPTH_CONV NUM_ADD_CONV) in
  let cr_step g = nred_cr (SPECL [`m:int32 list`; `l:int32 list`; mk_small_numeral g]
                            CR4_SPEC_STEP_WWIN) in
  let cr52 = cr_step 13 and cr56 = cr_step 14 and cr60 = cr_step 15 in
  let wring40 = nred_off (SPECL [`m:int32 list`; `40`] WRING_WWIN) in
  let wring44 = nred_off (SPECL [`m:int32 list`; `44`] WRING_WWIN) in
  let padp44  = GSYM(nred_off (SPECL [`m:int32 list`; `44`] PADP)) in
  let stepA = REWRITE_RULE[wring40; padp44; wring44; cr52; cr56] body' in
  let l60 = `sha256_compress_rounds m (l:int32 list) 60 : int32 list` in
  let wk15 = `simd4 word_add
     (WQUAD (EL 60 sha256_constants) (EL 61 sha256_constants)
            (EL 62 sha256_constants) (EL 63 sha256_constants))
     (WWIN m 60) : int128` in
  let GA = CONV_RULE(TOP_DEPTH_CONV let_CONV)
             (SPECL [l60; wk15] SHA256_RNDS2_GROUP_ADVANCE) in
  let GA1 = CONJUNCT1 GA and GA2 = CONJUNCT2 GA in
  let ATCF = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [l60;
             `word_subword (wk15v:int128) (0,32):int32`; `word_subword (wk15v:int128) (32,32):int32`;
             `word_subword (wk15v:int128) (64,32):int32`; `word_subword (wk15v:int128) (96,32):int32`]
            ABEF_TWO_IS_CDGH_FOUR) in
  let ATCF = INST [wk15, `wk15v:int128`] ATCF in
  let stepB0 = REWRITE_RULE[GA1] stepA in
  let stepB1 = REWRITE_RULE[GA2] stepB0 in
  let stepB  = REWRITE_RULE[ATCF] stepB1 in
  let stepC = REWRITE_RULE[cr60] (REWRITE_RULE[GSYM CR4] stepB) in
  let step2 = REWRITE_RULE[SIMD4_ADD_ABEF; SIMD4_ADD_CDGH] stepC in
  let step3 = REWRITE_RULE[GSYM BLOCK_ELS_L] step2 in
  GEN_ALL step3;;
Printf.printf "S055_CLB_SPEC_PLUS_RIP hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_CORE_LOOP_BODY_SPEC_PLUS_RIP))
  (List.length(frees(concl SHA256_COMPRESS_HW_CORE_LOOP_BODY_SPEC_PLUS_RIP)));;

(* --- Arithmetic bridges for the loop-index reconciliation in the body leg. --- *)
(* HB_STEP: hash_blocks(i+1) = block(m i)(hash_blocks i). *)
let SHA256_HW_HB_STEP = prove
 (`!(m:num->int32 list) (H:int32 list) i.
     sha256_hash_blocks m H (i + 1) =
     sha256_block (m i) (sha256_hash_blocks m H i)`,
  REWRITE_TAC[GSYM ADD1] THEN REWRITE_TAC[sha256_hash_blocks; ADD1]);;
(* RSI_STEP: (dptr+64i)+64 = dptr+64(i+1). *)
let SHA256_HW_RSI_STEP = prove
 (`!(dptr:int64) i.
     word_add (word_add dptr (word (64 * i))) (word 64) =
     word_add dptr (word (64 * (i + 1)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
  CONV_TAC WORD_RULE);;
(* RDX_STEP: word_sub (word(nb-i)) (word 1) = word(nb-(i+1)) given i<nb. *)
let SHA256_HW_RDX_STEP = prove
 (`!(num_blocks:num) i.
     i < num_blocks
     ==> word_sub (word (num_blocks - i):int64) (word 1) =
         word (num_blocks - (i + 1))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `num_blocks - i = (num_blocks - (i + 1)) + 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;
(* ZF_EXIT: (val(word_sub (word(nb-i)) (word 1)) = 0) <=> ~(i+1<nb), for nb<2^64. *)
let SHA256_HW_ZF_EXIT = prove
 (`!(num_blocks:num) i.
     i < num_blocks /\ num_blocks < 2 EXP 64
     ==> ((val (word_sub (word (num_blocks - i):int64) (word 1)) = 0) <=>
          ~(i + 1 < num_blocks))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`num_blocks:num`;`i:num`] SHA256_HW_RDX_STEP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `val (word (num_blocks - (i + 1)):int64) = num_blocks - (i + 1)`
    SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    TRANS_TAC LET_TRANS `num_blocks:num` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  ARITH_TAC);;
Printf.printf "S055_BRIDGES hb=%d rsi=%d rdx=%d zf=%d\n%!"
  (List.length(hyp SHA256_HW_HB_STEP)) (List.length(hyp SHA256_HW_RSI_STEP))
  (List.length(hyp SHA256_HW_RDX_STEP)) (List.length(hyp SHA256_HW_ZF_EXIT));;
Printf.printf "S055_RIP_AND_BRIDGES_DONE\n%!";;

(* ========================================================================= *)
(* Session 054 -- CORE_CORRECT scaffold: the multi-block core loop           *)
(* (pc+0x07 -> pc+0x334) via ENSURES_WHILE_UP2_TAC over the jne@pc+0x30c      *)
(* back-edge.  JNE_BR = the abstract-ZF conditional back-edge primitive       *)
(* (ZF set -> fall through pc+0x312, ZF clear -> loop head pc+0x38).          *)
(* The three loop legs (entry seam ENTRY_REPACK -> loopinv 0; body via        *)
(* CORE_LOOP_BODY_SPEC_PLUS ; JNE_BR; exit JNE_FALLTHRU ; EXIT) are CHEATed    *)
(* in this scaffold and discharged incrementally.  Loop invariant @pc+0x38:   *)
(* YMM1/2 = ABEF/CDGH_PACK(sha256_hash_blocks m H i), RSI=dptr+64i,            *)
(* RDX=word(num_blocks-i), YMM7=YMM8=mask, 16 K-quads, quantified per-block    *)
(* big-endian message memory.                                                 *)
(* ========================================================================= *)
(* First: the JNE_BR primitive (abstract-ZF conditional back-edge). *)
let SHA256_COMPRESS_HW_JNE_BR = prove
 (`!pc kbase (zf:bool).
     ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
            read RIP s = word (pc + 0x30c) /\
            (read ZF s <=> zf))
       (\s. read RIP s = (if zf then word (pc + 0x312) else word (pc + 0x38)))
       (MAYCHANGE [RIP] ,, MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_EXEC "s1" THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;
Printf.printf "S054_JNE_BR hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_JNE_BR))
  (List.length(frees(concl SHA256_COMPRESS_HW_JNE_BR)));;

(* --- CORE_LOOP_STEP_RAW = CLB_SPEC_PLUS_RIP ; JNE_BR, per-block (no loop      *)
(* index / quantifier).  PRE = CLB_SPEC_PLUS_RIP.PRE @pc+0x38; POST = CLB POST   *)
(* with RIP -> the JNE_BR conditional (if val(word_sub rdxin 1)=0 then pc+0x312  *)
(* else pc+0x38).  This is the raw single-iteration transition the UP2 body leg  *)
(* instantiates (l:=hash_blocks m H i, m:=m i, mptr:=dptr+64i,                    *)
(* rdxin:=word(num_blocks-i)); the loop-index reconciliation to loopinv(i+1) is  *)
(* then just the 4 arithmetic bridges + HB_STEP.                                 *)
let SHA256_COMPRESS_HW_CORE_LOOP_STEP_RAW =
  let clb = SPEC_ALL SHA256_COMPRESS_HW_CORE_LOOP_BODY_SPEC_PLUS_RIP in
  let clb_body = snd(strip_forall(concl clb)) in
  let clb_ant, clb_ens = dest_imp clb_body in
  let clb_pre  = rand(rator(rator clb_ens)) in
  let clb_post = rand(rator clb_ens) in
  let clb_frame = rand clb_ens in
  let clb_post_conjs = conjuncts(snd(dest_abs clb_post)) in
  (* c is `read RIP s = ...` iff its LHS is `read RIP s` (rator = `read RIP`,   *)
  (* itself `read` applied to the component `RIP`).  string_of_term match is     *)
  (* robust to the read/RIP being combs (dest_const on `read RIP` throws).       *)
  let is_rip c =
    (try string_of_term(rand(rator(lhs c))) = "RIP" with _ -> false) in
  let non_rip = filter (fun c -> not(is_rip c)) clb_post_conjs in
  let jne_rip = `read RIP s =
     (if (val (word_sub (rdxin:int64) (word 1)) = 0)
      then word (pc + 0x312) else word (pc + 0x38))` in
  let step_post = mk_abs(`s:x86state`, list_mk_conj (jne_rip :: non_rip)) in
  let ens_head = rator(rator(rator clb_ens)) in
  let step_ens = mk_comb(mk_comb(mk_comb(ens_head, clb_pre), step_post), clb_frame) in
  let step_bvars = [`kbase:num`;`pc:num`;`kptr:int64`;`rdxin:int64`;
                    `m:int32 list`;`l:int32 list`;`mptr:int64`] in
  let step_concl = list_mk_forall(step_bvars, mk_imp(clb_ant, step_ens)) in
  (* seam @pc+0x30c = clb_post MINUS its RIP conjunct (ENSURES_SEQUENCE_TAC        *)
  (* auto-injects read RIP s = word pc'; leaving it in the seam duplicates RIP and *)
  (* leaves the spurious residual `(if ... then pc+786 else pc+56) = word(pc+780)`).*)
  let seam = mk_abs(`s:x86state`,
               list_mk_conj (filter (fun c -> not(is_rip c))
                              (conjuncts(snd(dest_abs clb_post))))) in
  let jne_inst = SPECL [`pc:num`;`kbase:num`;
                        `val (word_sub (rdxin:int64) (word 1)) = 0`]
                   SHA256_COMPRESS_HW_JNE_BR in
  prove
   (step_concl,
    REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
    ENSURES_SEQUENCE_TAC `pc + 0x30c` seam THEN CONJ_TAC THENL
     [MP_TAC(REWRITE_RULE[SOME_FLAGS] clb) THEN ASM_REWRITE_TAC[] THEN
      (ENSURES_SUBLEMMA_TAC execup "s" "s'" ORELSE
       ENSURES_SUBLEMMA_REFL_TAC execup "s" "s'") THEN ASM_REWRITE_TAC[];
      MP_TAC jne_inst THEN ASM_REWRITE_TAC[] THEN
      (ENSURES_SUBLEMMA_TAC execup "s" "s'" ORELSE
       ENSURES_SUBLEMMA_REFL_TAC execup "s" "s'") THEN ASM_REWRITE_TAC[]]);;
Printf.printf "S055_CORE_LOOP_STEP_RAW hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_CORE_LOOP_STEP_RAW))
  (List.length(frees(concl SHA256_COMPRESS_HW_CORE_LOOP_STEP_RAW)));;

(* --- The CORE_CORRECT statement.  m : num->int32 list is the block-indexed  *)
(* message function (m i = the 16 dwords of block i).  H : int32 list = the    *)
(* 8-word input state.  dptr = data pointer, sptr = state pointer (RDI).       *)
(* Message memory: per-quad bytes128 big-endian reads for each block.          *)
let core_correct_tm = `
 !pc kbase (kptr:int64) (sptr:int64) (dptr:int64) (H:int32 list)
   (m:num->int32 list) (num_blocks:num).
   aligned 16 kptr /\
   aligned 16 (word_add kptr (word 384)) /\
   aligned 16 (word_add kptr (word 18446744073709551488)) /\
   aligned 16 (word_add kptr (word 18446744073709551520)) /\
   aligned 16 (word_add kptr (word 18446744073709551552)) /\
   aligned 16 (word_add kptr (word 18446744073709551584)) /\
   0 < num_blocks /\
   val (dptr:int64) + 64 * num_blocks < 2 EXP 64 /\
   nonoverlapping (word pc,825) (sptr,32)
   ==> ensures x86
     (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
          read RIP s = word (pc + 0x07) /\
          read RCX s = kptr /\
          read RDI s = sptr /\
          read RSI s = dptr /\
          read RDX s = word num_blocks /\
          read (memory :> bytes128 (word_add kptr (word 384))) s =
            word 16018520953223639909183530438118932995 /\
          read (memory :> bytes128 sptr) s =
            WQUAD (EL 0 H) (EL 1 H) (EL 2 H) (EL 3 H) /\
          read (memory :> bytes128 (word_add sptr (word 16))) s =
            WQUAD (EL 4 H) (EL 5 H) (EL 6 H) (EL 7 H) /\
          read (memory :> bytes128 (word_add kptr (word 18446744073709551488))) s =
            WQUAD (EL 0 sha256_constants) (EL 1 sha256_constants)
                  (EL 2 sha256_constants) (EL 3 sha256_constants) /\
          read (memory :> bytes128 (word_add kptr (word 18446744073709551520))) s =
            WQUAD (EL 4 sha256_constants) (EL 5 sha256_constants)
                  (EL 6 sha256_constants) (EL 7 sha256_constants) /\
          read (memory :> bytes128 (word_add kptr (word 18446744073709551552))) s =
            WQUAD (EL 8 sha256_constants) (EL 9 sha256_constants)
                  (EL 10 sha256_constants) (EL 11 sha256_constants) /\
          read (memory :> bytes128 (word_add kptr (word 18446744073709551584))) s =
            WQUAD (EL 12 sha256_constants) (EL 13 sha256_constants)
                  (EL 14 sha256_constants) (EL 15 sha256_constants) /\
          read (memory :> bytes128 kptr) s =
            WQUAD (EL 16 sha256_constants) (EL 17 sha256_constants)
                  (EL 18 sha256_constants) (EL 19 sha256_constants) /\
          read (memory :> bytes128 (word_add kptr (word 32))) s =
            WQUAD (EL 20 sha256_constants) (EL 21 sha256_constants)
                  (EL 22 sha256_constants) (EL 23 sha256_constants) /\
          read (memory :> bytes128 (word_add kptr (word 64))) s =
            WQUAD (EL 24 sha256_constants) (EL 25 sha256_constants)
                  (EL 26 sha256_constants) (EL 27 sha256_constants) /\
          read (memory :> bytes128 (word_add kptr (word 96))) s =
            WQUAD (EL 28 sha256_constants) (EL 29 sha256_constants)
                  (EL 30 sha256_constants) (EL 31 sha256_constants) /\
          read (memory :> bytes128 (word_add kptr (word 128))) s =
            WQUAD (EL 32 sha256_constants) (EL 33 sha256_constants)
                  (EL 34 sha256_constants) (EL 35 sha256_constants) /\
          read (memory :> bytes128 (word_add kptr (word 160))) s =
            WQUAD (EL 36 sha256_constants) (EL 37 sha256_constants)
                  (EL 38 sha256_constants) (EL 39 sha256_constants) /\
          read (memory :> bytes128 (word_add kptr (word 192))) s =
            WQUAD (EL 40 sha256_constants) (EL 41 sha256_constants)
                  (EL 42 sha256_constants) (EL 43 sha256_constants) /\
          read (memory :> bytes128 (word_add kptr (word 224))) s =
            WQUAD (EL 44 sha256_constants) (EL 45 sha256_constants)
                  (EL 46 sha256_constants) (EL 47 sha256_constants) /\
          read (memory :> bytes128 (word_add kptr (word 256))) s =
            WQUAD (EL 48 sha256_constants) (EL 49 sha256_constants)
                  (EL 50 sha256_constants) (EL 51 sha256_constants) /\
          read (memory :> bytes128 (word_add kptr (word 288))) s =
            WQUAD (EL 52 sha256_constants) (EL 53 sha256_constants)
                  (EL 54 sha256_constants) (EL 55 sha256_constants) /\
          read (memory :> bytes128 (word_add kptr (word 320))) s =
            WQUAD (EL 56 sha256_constants) (EL 57 sha256_constants)
                  (EL 58 sha256_constants) (EL 59 sha256_constants) /\
          read (memory :> bytes128 (word_add kptr (word 352))) s =
            WQUAD (EL 60 sha256_constants) (EL 61 sha256_constants)
                  (EL 62 sha256_constants) (EL 63 sha256_constants) /\
          (!j. j < num_blocks
               ==> read (memory :> bytes128 (word_add dptr (word (64 * j)))) s =
                     WQUAD (word_bytereverse (EL 0 (m j))) (word_bytereverse (EL 1 (m j)))
                           (word_bytereverse (EL 2 (m j))) (word_bytereverse (EL 3 (m j))) /\
                   read (memory :> bytes128 (word_add dptr (word (64 * j + 16)))) s =
                     WQUAD (word_bytereverse (EL 4 (m j))) (word_bytereverse (EL 5 (m j)))
                           (word_bytereverse (EL 6 (m j))) (word_bytereverse (EL 7 (m j))) /\
                   read (memory :> bytes128 (word_add dptr (word (64 * j + 32)))) s =
                     WQUAD (word_bytereverse (EL 8 (m j))) (word_bytereverse (EL 9 (m j)))
                           (word_bytereverse (EL 10 (m j))) (word_bytereverse (EL 11 (m j))) /\
                   read (memory :> bytes128 (word_add dptr (word (64 * j + 48)))) s =
                     WQUAD (word_bytereverse (EL 12 (m j))) (word_bytereverse (EL 13 (m j)))
                           (word_bytereverse (EL 14 (m j))) (word_bytereverse (EL 15 (m j)))))
     (\s. read RIP s = word (pc + 0x334) /\
          read RDI s = sptr /\
          read (memory :> bytes128 sptr) s =
            WQUAD (EL 0 (sha256_hash_blocks m H num_blocks))
                  (EL 1 (sha256_hash_blocks m H num_blocks))
                  (EL 2 (sha256_hash_blocks m H num_blocks))
                  (EL 3 (sha256_hash_blocks m H num_blocks)) /\
          read (memory :> bytes128 (word_add sptr (word 16))) s =
            WQUAD (EL 4 (sha256_hash_blocks m H num_blocks))
                  (EL 5 (sha256_hash_blocks m H num_blocks))
                  (EL 6 (sha256_hash_blocks m H num_blocks))
                  (EL 7 (sha256_hash_blocks m H num_blocks)))
     (MAYCHANGE [RIP; RSI; RDX] ,,
      MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM5_SSE;
                 YMM6_SSE; YMM7_SSE; YMM8_SSE; YMM9_SSE; YMM10_SSE] ,,
      MAYCHANGE [memory :> bytes128 sptr;
                 memory :> bytes128 (word_add sptr (word 16))] ,,
      MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`;;
Printf.printf "S054_CC_STATEMENT_PARSED frees=%d\n%!" (List.length(frees core_correct_tm));;
Printf.printf "S054_CC_STATEMENT_DONE\n%!";;

(* --- Loop invariant at pc+0x38 for iteration i (0<=i<=num_blocks). --- *)
let loopinv_tm = `
 \(i:num) s.
   read RCX s = kptr /\
   read RDI s = sptr /\
   read RSI s = word_add dptr (word (64 * i)) /\
   read RDX s = word (num_blocks - i) /\
   word_subword (read YMM1_SSE s) (0,128) =
     ABEF_PACK (EL 0 (sha256_hash_blocks m H i)) (EL 1 (sha256_hash_blocks m H i))
               (EL 4 (sha256_hash_blocks m H i)) (EL 5 (sha256_hash_blocks m H i)) /\
   word_subword (read YMM2_SSE s) (0,128) =
     CDGH_PACK (EL 2 (sha256_hash_blocks m H i)) (EL 3 (sha256_hash_blocks m H i))
               (EL 6 (sha256_hash_blocks m H i)) (EL 7 (sha256_hash_blocks m H i)) /\
   word_subword (read YMM7_SSE s) (0,128) =
     word 16018520953223639909183530438118932995 : int128 /\
   word_subword (read YMM8_SSE s) (0,128) =
     word 16018520953223639909183530438118932995 : int128 /\
   read (memory :> bytes128 (word_add kptr (word 18446744073709551488))) s =
     WQUAD (EL 0 sha256_constants) (EL 1 sha256_constants)
           (EL 2 sha256_constants) (EL 3 sha256_constants) /\
   read (memory :> bytes128 (word_add kptr (word 18446744073709551520))) s =
     WQUAD (EL 4 sha256_constants) (EL 5 sha256_constants)
           (EL 6 sha256_constants) (EL 7 sha256_constants) /\
   read (memory :> bytes128 (word_add kptr (word 18446744073709551552))) s =
     WQUAD (EL 8 sha256_constants) (EL 9 sha256_constants)
           (EL 10 sha256_constants) (EL 11 sha256_constants) /\
   read (memory :> bytes128 (word_add kptr (word 18446744073709551584))) s =
     WQUAD (EL 12 sha256_constants) (EL 13 sha256_constants)
           (EL 14 sha256_constants) (EL 15 sha256_constants) /\
   read (memory :> bytes128 kptr) s =
     WQUAD (EL 16 sha256_constants) (EL 17 sha256_constants)
           (EL 18 sha256_constants) (EL 19 sha256_constants) /\
   read (memory :> bytes128 (word_add kptr (word 32))) s =
     WQUAD (EL 20 sha256_constants) (EL 21 sha256_constants)
           (EL 22 sha256_constants) (EL 23 sha256_constants) /\
   read (memory :> bytes128 (word_add kptr (word 64))) s =
     WQUAD (EL 24 sha256_constants) (EL 25 sha256_constants)
           (EL 26 sha256_constants) (EL 27 sha256_constants) /\
   read (memory :> bytes128 (word_add kptr (word 96))) s =
     WQUAD (EL 28 sha256_constants) (EL 29 sha256_constants)
           (EL 30 sha256_constants) (EL 31 sha256_constants) /\
   read (memory :> bytes128 (word_add kptr (word 128))) s =
     WQUAD (EL 32 sha256_constants) (EL 33 sha256_constants)
           (EL 34 sha256_constants) (EL 35 sha256_constants) /\
   read (memory :> bytes128 (word_add kptr (word 160))) s =
     WQUAD (EL 36 sha256_constants) (EL 37 sha256_constants)
           (EL 38 sha256_constants) (EL 39 sha256_constants) /\
   read (memory :> bytes128 (word_add kptr (word 192))) s =
     WQUAD (EL 40 sha256_constants) (EL 41 sha256_constants)
           (EL 42 sha256_constants) (EL 43 sha256_constants) /\
   read (memory :> bytes128 (word_add kptr (word 224))) s =
     WQUAD (EL 44 sha256_constants) (EL 45 sha256_constants)
           (EL 46 sha256_constants) (EL 47 sha256_constants) /\
   read (memory :> bytes128 (word_add kptr (word 256))) s =
     WQUAD (EL 48 sha256_constants) (EL 49 sha256_constants)
           (EL 50 sha256_constants) (EL 51 sha256_constants) /\
   read (memory :> bytes128 (word_add kptr (word 288))) s =
     WQUAD (EL 52 sha256_constants) (EL 53 sha256_constants)
           (EL 54 sha256_constants) (EL 55 sha256_constants) /\
   read (memory :> bytes128 (word_add kptr (word 320))) s =
     WQUAD (EL 56 sha256_constants) (EL 57 sha256_constants)
           (EL 58 sha256_constants) (EL 59 sha256_constants) /\
   read (memory :> bytes128 (word_add kptr (word 352))) s =
     WQUAD (EL 60 sha256_constants) (EL 61 sha256_constants)
           (EL 62 sha256_constants) (EL 63 sha256_constants) /\
   (!j. j < num_blocks
        ==> read (memory :> bytes128 (word_add dptr (word (64 * j)))) s =
              WQUAD (word_bytereverse (EL 0 (m j))) (word_bytereverse (EL 1 (m j)))
                    (word_bytereverse (EL 2 (m j))) (word_bytereverse (EL 3 (m j))) /\
            read (memory :> bytes128 (word_add dptr (word (64 * j + 16)))) s =
              WQUAD (word_bytereverse (EL 4 (m j))) (word_bytereverse (EL 5 (m j)))
                    (word_bytereverse (EL 6 (m j))) (word_bytereverse (EL 7 (m j))) /\
            read (memory :> bytes128 (word_add dptr (word (64 * j + 32)))) s =
              WQUAD (word_bytereverse (EL 8 (m j))) (word_bytereverse (EL 9 (m j)))
                    (word_bytereverse (EL 10 (m j))) (word_bytereverse (EL 11 (m j))) /\
            read (memory :> bytes128 (word_add dptr (word (64 * j + 48)))) s =
              WQUAD (word_bytereverse (EL 12 (m j))) (word_bytereverse (EL 13 (m j)))
                    (word_bytereverse (EL 14 (m j))) (word_bytereverse (EL 15 (m j))))`;;
Printf.printf "S054_LOOPINV_PARSED frees=%d\n%!" (List.length(frees loopinv_tm));;

(* word_subword of a WQUAD picks out the k-th dword (used to reduce ENTRY_REPACK's *)
(* q0/q1-subword packs to packs of EL H at the i=0 entry seam).                    *)
let WQUAD_SUBWORD = prove
 (`!a b c d:int32.
     word_subword (WQUAD a b c d) (0,32) = a /\
     word_subword (WQUAD a b c d) (32,32) = b /\
     word_subword (WQUAD a b c d) (64,32) = c /\
     word_subword (WQUAD a b c d) (96,32) = d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WQUAD] THEN CONV_TAC WORD_BLAST);;

(* Body-leg address/branch closers.                                             *)
(* MSG_ADDR: normalize the per-quad message address the loop invariant's         *)
(* quantified conjunct produces (word_add dptr (word(64*i+k))) to the nested     *)
(* form CORE_LOOP_STEP_RAW's PRE reads (word_add (word_add dptr (word(64*i)))    *)
(* (word k)).                                                                    *)
let MSG_ADDR = prove
 (`!(dptr:int64) i k.
     word_add (word_add dptr (word (64 * i))) (word k) =
     word_add dptr (word (64 * i + k))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;
(* RIP_COND: reconcile CORE_LOOP_STEP_RAW's ZF-driven back-edge target            *)
(* (if val(word(nb-(i+1)))=0 then pc+0x312 else pc+0x38) with the UP2 body        *)
(* postcondition's target (word(if i+1<nb then pc+0x38 else pc+0x312)).  Requires *)
(* nb<2^64 so word(nb-(i+1)) does not wrap: val = nb-(i+1), which is 0 iff        *)
(* ~(i+1<nb).  (pc+786 = pc+0x312, pc+56 = pc+0x38.)                              *)
let RIP_COND = prove
 (`!(num_blocks:num) i pc.
     i < num_blocks /\ num_blocks < 2 EXP 64
     ==> (if val (word (num_blocks - (i + 1)):int64) = 0
          then word (pc + 786) else word (pc + 56)) =
         word (if i + 1 < num_blocks then pc + 56 else pc + 786)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val (word (num_blocks - (i + 1)):int64) = num_blocks - (i + 1)`
    SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    TRANS_TAC LET_TRANS `num_blocks:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(num_blocks - (i + 1) = 0) <=> ~(i + 1 < num_blocks)` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(* CORE_CORRECT: the multi-block core, pc+0x07 -> pc+0x334.  ENTRY_REPACK (once,  *)
(* i=0 seam) ; ENSURES_WHILE_UP2 over the jne@pc+0x30c back-edge with body =      *)
(* CORE_LOOP_STEP_RAW (per-iteration l:=hash_blocks m H i, block i, ptr dptr+64i, *)
(* count word(nb-i)) reconciled to loopinv(i+1) via HB_STEP/RSI_STEP/RDX_STEP/    *)
(* RIP_COND/MSG_ADDR ; EXIT store.  All three legs discharged (no CHEAT).         *)
let SHA256_COMPRESS_HW_CORE_CORRECT = prove
 (core_correct_tm,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  SUBGOAL_THEN `~(num_blocks = 0)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ENSURES_WHILE_UP2_TAC `num_blocks:num` `pc + 0x38` `pc + 0x312` loopinv_tm THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ (* ENTRY leg: ENTRY_REPACK (sptr as its dptr, q0/q1 = the H WQUADs) *)
     MP_TAC(ISPECL
       [`pc:num`;`kbase:num`;`kptr:int64`;`sptr:int64`;
        `WQUAD (EL 0 H) (EL 1 H) (EL 2 H) (EL 3 H):int128`;
        `WQUAD (EL 4 H) (EL 5 H) (EL 6 H) (EL 7 H):int128`;
        `word 16018520953223639909183530438118932995:int128`]
       SHA256_COMPRESS_HW_ENTRY_REPACK) THEN
     ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[sha256_hash_blocks; SUB_0; MULT_CLAUSES; WORD_ADD_0;
                 WQUAD_SUBWORD] THEN
     ENSURES_SUBLEMMA_TAC execup "s" "s'" THEN
     ASM_REWRITE_TAC[WQUAD_SUBWORD];
     (* BODY leg (pc+0x38 loopinv i -> (if i+1<nb then pc+0x38 else pc+0x312)    *)
     (* loopinv(i+1)).  s055: discharged.  Compose CORE_LOOP_STEP_RAW (= one     *)
     (* loop iteration CLB_SPEC_PLUS_RIP ; JNE_BR) instantiated at l:=            *)
     (* hash_blocks m H i, block i, ptr dptr+64i, count word(nb-i), lift via the *)
     (* SUBLEMMA, reconcile:                                                     *)
     (*   pre  (loopinv i => STEP_PRE): specialize the quantified message        *)
     (*        conjunct at j:=i (ASM_SIMP) + normalize addresses (MSG_ADDR).      *)
     (*   post (STEP_POST => loopinv(i+1)): HB_STEP folds block(m i)(hb i)->      *)
     (*        hb(i+1); RSI_STEP/RDX_STEP the pointer/counter; RIP_COND the       *)
     (*        ZF-driven back-edge target.  RDI/K/message ride the frame.         *)
     REPEAT STRIP_TAC THEN
     SUBGOAL_THEN `num_blocks < 2 EXP 64` ASSUME_TAC THENL
      [TRANS_TAC LET_TRANS `val (dptr:int64) + 64 * num_blocks` THEN
       ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
     MP_TAC(REWRITE_RULE[SOME_FLAGS]
       (SPECL [`kbase:num`;`pc:num`;`kptr:int64`;`word (num_blocks - i):int64`;
               `(m:num->int32 list) i`; `sha256_hash_blocks m H i`;
               `word_add dptr (word (64 * i)):int64`]
          SHA256_COMPRESS_HW_CORE_LOOP_STEP_RAW)) THEN
     ASM_REWRITE_TAC[] THEN
     (ENSURES_SUBLEMMA_TAC execup "s" "s'" ORELSE
      ENSURES_SUBLEMMA_REFL_TAC execup "s" "s'") THENL
      [ ASM_SIMP_TAC[MSG_ADDR];
        REWRITE_TAC[SHA256_HW_HB_STEP] THEN
        ASM_SIMP_TAC[SHA256_HW_RSI_STEP; SHA256_HW_RDX_STEP; RIP_COND] ];
     (* EXIT leg (pc+0x312 loopinv num_blocks -> pc+0x334, EXIT + store).       *)
     (* s055: discharged.  Mirror the proven single-block CORE_BODY leg_tac      *)
     (* (line ~7518): instantiate EXIT with abef/cdgh := the hash_blocks packs,  *)
     (* MP_TAC with SOME_FLAGS expanded so ASM_REWRITE discharges EXIT's          *)
     (* nonoverlapping antecedent (the s054 No-match was an undischarged          *)
     (* antecedent + missing REFL fallback, not the math), then the SUBLEMMA      *)
     (* lift (ORELSE reflexive), then close the stored WQUADs via                 *)
     (* ABEF/CDGH_PACK_SUBWORDS.                                                  *)
     MP_TAC(REWRITE_RULE[SOME_FLAGS]
       (SPECL [`pc:num`;`kbase:num`;`sptr:int64`;
          `ABEF_PACK (EL 0 (sha256_hash_blocks m H num_blocks))
                     (EL 1 (sha256_hash_blocks m H num_blocks))
                     (EL 4 (sha256_hash_blocks m H num_blocks))
                     (EL 5 (sha256_hash_blocks m H num_blocks)):int128`;
          `CDGH_PACK (EL 2 (sha256_hash_blocks m H num_blocks))
                     (EL 3 (sha256_hash_blocks m H num_blocks))
                     (EL 6 (sha256_hash_blocks m H num_blocks))
                     (EL 7 (sha256_hash_blocks m H num_blocks)):int128`]
          SHA256_COMPRESS_HW_EXIT)) THEN
     ASM_REWRITE_TAC[] THEN
     (ENSURES_SUBLEMMA_TAC execup "s" "s'" ORELSE
      ENSURES_SUBLEMMA_REFL_TAC execup "s" "s'") THEN
     ASM_REWRITE_TAC[ABEF_PACK_SUBWORDS; CDGH_PACK_SUBWORDS] ]);;
Printf.printf "S055_CORE_CORRECT hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_CORE_CORRECT))
  (List.length(frees(concl SHA256_COMPRESS_HW_CORE_CORRECT)));;
Printf.printf "S055_CORE_CORRECT_DONE\n%!";;

(* ========================================================================= *)
(* Phase 7 — SysV subroutine CORRECT (NOIBT + IBT).                          *)
(*                                                                           *)
(* Unlike the scalar nohw routine, the hw code is a LEAF function with NO    *)
(* stack frame, no callee-saved GPR pushes and no scratch memory on SysV.    *)
(* The only "prologue" is a single RIP-relative load of the K256 table base  *)
(* into RCX:                                                                 *)
(*     (pc+0x00)  lea  rcx,[rip+K256+128]   (7 bytes; rcx := K256 + 128)     *)
(* after which the core body runs pc+0x07 .. pc+0x334 and returns via a bare *)
(* `ret` at pc+0x334.  CORE_CORRECT (above) assumes RCX = kptr and the 16    *)
(* round-constant WQUAD rows + byteswap mask are already present in memory;  *)
(* the subroutine wrapper establishes them from a whole-rodata `bytes_loaded *)
(* (word kk) K256` precondition (kk = the K256 symbol address), executing    *)
(* the lea (which folds to kptr = word_add (word kk) (word 128)) and         *)
(* deriving the K/mask reads with SHA256_HW_K256_WQUAD_READS below.          *)
(* ------------------------------------------------------------------------- *)

(* K256 length as a numeral (|- LENGTH K256 = 608). *)
let HW_LEN_K256 = CONV_RULE (RAND_CONV LENGTH_CONV)
                 (AP_TERM `LENGTH:byte list->num` K256_DATA);;

(* bytes_loaded whole-rodata <=> a bytes read of the K256 blob. *)
let HW_K_BYTES_FORM = prove
 (`bytes_loaded s (word kk:int64) K256 <=>
   read (memory :> bytes (word kk:int64,608)) s = num_of_bytelist K256`,
  REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES; HW_LEN_K256]);;

(* Helper tactics (lifted verbatim from x86/tutorial/rodata.ml, as in the     *)
(* nohw proof): explode the whole-rodata bytelist assumption to per-byte      *)
(* bytes8 reads, then assemble each bytes128 row from its component bytes.    *)
let INTRO_READ_MEMORY_FROM_BYTES8_TAC (t:term) =
  let r = REWRITE_CONV [READ_MEMORY_BYTESIZED_SPLIT] t in
  let r = REWRITE_RULE[WORD_ADD_ASSOC_CONSTS;WORD_ADD_0;ARITH] r in
  MP_TAC r THEN
  ASM (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)) [] THEN
  CONV_TAC (LAND_CONV WORD_REDUCE_CONV) THEN
  DISCH_TAC;;

let EXPLODE_BYTELIST_ASSUM_TAC const_data =
  FIRST_X_ASSUM (fun th ->
    let _ = find_term (fun t -> name_of t = "bytelist") (concl th) in
    let unfolded_bytes_loaded = REWRITE_RULE const_data th in
    MP_TAC (CONV_RULE (ONCE_DEPTH_CONV LENGTH_CONV THENC
                      LAND_CONV BYTELIST_EXPAND_CONV)
            unfolded_bytes_loaded)) THEN
  REWRITE_TAC [CONS_11] THEN
  STRIP_TAC;;

(* From the whole-rodata bytelist precondition on the K256 blob at base kk,   *)
(* derive the 16 bytes128 round-constant WQUAD rows (row g at byte offset     *)
(* 32*g = WQUAD (EL 4g..4g+3) sha256_constants, the doubled-row layout) plus  *)
(* the byteswap mask (bytes128 at kk+512).  Keyed on `word_add (word kk)      *)
(* (word M)` (M = 0,32,..,512).  bytes128/WQUAD analog of nohw's per-dword     *)
(* SHA256_K256_READS.  The CORE_CORRECT precondition states these same reads   *)
(* in the kptr-relative form `word_add (word_add (word kk)(word 128))(word     *)
(* DISP)`; the subroutine wrapper bridges the two via SHA256_HW_KADDR_NORM     *)
(* (17 WORD_BLAST address equalities).                                         *)
let SHA256_HW_K256_WQUAD_READS =
  let one g =
    Printf.sprintf
      "read (memory :> bytes128 (word_add (word kk) (word %d))) s = \
         WQUAD (EL %d sha256_constants) (EL %d sha256_constants) \
               (EL %d sha256_constants) (EL %d sha256_constants)"
      (32*g) (4*g) (4*g+1) (4*g+2) (4*g+3) in
  let rows = String.concat " /\\ " (map one (0--15)) in
  let mask =
    "read (memory :> bytes128 (word_add (word kk) (word 512))) s = \
       (word 16018520953223639909183530438118932995:int128)" in
  let body = rows ^ " /\\ " ^ mask in
  let goal = parse_term (Printf.sprintf
    "!kk:num s:x86state. \
       read (memory :> bytelist (word kk, LENGTH K256)) s = K256 \
       ==> %s" body) in
  prove
   (goal,
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    EXPLODE_BYTELIST_ASSUM_TAC [K256_DATA] THEN
    REWRITE_TAC[sha256_constants; WQUAD] THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN
    REPEAT CONJ_TAC THEN
    (fun (asl,w) -> INTRO_READ_MEMORY_FROM_BYTES8_TAC (lhs w) (asl,w)) THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_BLAST);;

Printf.printf "S056_K256_WQUAD_READS hyps=%d\n%!"
  (List.length(hyp SHA256_HW_K256_WQUAD_READS));;

(* 17 address equalities normalizing the CORE_CORRECT kptr-relative K/mask     *)
(* addresses (word_add (word_add (word kk)(word 128))(word DISP)) to the       *)
(* bridge's `word_add (word kk)(word M)` form.  Proved by WORD_BLAST (handles  *)
(* the g=0..3 mod-2^64 wrap that WORD_RULE cannot).  Used to rewrite the       *)
(* subroutine wrapper's core-PRE match onto SHA256_HW_K256_WQUAD_READS.        *)
let SHA256_HW_KADDR_NORM =
  let disp_str g =
    if g >= 4 then string_of_int (32*g - 128)
    else [| "18446744073709551488"; "18446744073709551520";
            "18446744073709551552"; "18446744073709551584" |].(g) in
  let one g = Printf.sprintf
    "word_add (word_add (word kk) (word 128)) (word %s):int64 = \
     word_add (word kk) (word %d)" (disp_str g) (32*g) in
  let maskeq =
    "word_add (word_add (word kk) (word 128)) (word 384):int64 = \
     word_add (word kk) (word 512)" in
  let body = String.concat " /\\ " (map one (0--15)) ^ " /\\ " ^ maskeq in
  let goal = parse_term (Printf.sprintf "!kk:num. %s" body) in
  prove(goal, GEN_TAC THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

Printf.printf "S056_KADDR_NORM hyps=%d\n%!"
  (List.length(hyp SHA256_HW_KADDR_NORM));;

(* The 6 kptr-relative alignments the CORE_CORRECT precondition needs, all     *)
(* derivable from `aligned 16 (word kk)` (kptr = kk+128, 128 = 8*16, and every  *)
(* displacement is a multiple of 16).                                          *)
let SHA256_HW_KPTR_ALIGN = prove
 (`aligned 16 (word kk:int64)
   ==> aligned 16 (word_add (word kk) (word 128):int64) /\
       aligned 16 (word_add (word_add (word kk) (word 128)) (word 384):int64) /\
       aligned 16 (word_add (word_add (word kk) (word 128)) (word 18446744073709551488):int64) /\
       aligned 16 (word_add (word_add (word kk) (word 128)) (word 18446744073709551520):int64) /\
       aligned 16 (word_add (word_add (word kk) (word 128)) (word 18446744073709551552):int64) /\
       aligned 16 (word_add (word_add (word kk) (word 128)) (word 18446744073709551584):int64)`,
  DISCH_TAC THEN REPEAT CONJ_TAC THEN
  ASM_REWRITE_TAC[NORMALIZE_ALIGNED_WORD_CONV
    `aligned 16 (word_add (word kk) (word 128):int64)`] THEN
  ASM_REWRITE_TAC[NORMALIZE_ALIGNED_WORD_CONV
    `aligned 16 (word_add (word_add (word kk) (word 128)) (word 384):int64)`] THEN
  ASM_REWRITE_TAC[NORMALIZE_ALIGNED_WORD_CONV
    `aligned 16 (word_add (word_add (word kk) (word 128)) (word 18446744073709551488):int64)`] THEN
  ASM_REWRITE_TAC[NORMALIZE_ALIGNED_WORD_CONV
    `aligned 16 (word_add (word_add (word kk) (word 128)) (word 18446744073709551520):int64)`] THEN
  ASM_REWRITE_TAC[NORMALIZE_ALIGNED_WORD_CONV
    `aligned 16 (word_add (word_add (word kk) (word 128)) (word 18446744073709551552):int64)`] THEN
  ASM_REWRITE_TAC[NORMALIZE_ALIGNED_WORD_CONV
    `aligned 16 (word_add (word_add (word kk) (word 128)) (word 18446744073709551584):int64)`]);;

(* The lea prologue fold: `lea rcx,[rip+K256+128]` (tmc offset 0, decoded reloc *)
(* addend 124) establishes rcx = word_add (word kk) (word 128) = kptr, where    *)
(* the wrapper parameterizes the frozen code as `sha256_compress_hw_tmc pc      *)
(* (kk + 4)` (the define_assert_relocs kbase = the K256 symbol address kk + 4). *)
(* Second (local-symbol) clause of RIP_REL_ADDR_FOLD, ofs=7, ofs2=117.          *)
let SHA256_HW_LEA_FOLD = prove
 (`!pc kk. riprel32_within_bounds (kk + 128) (pc + 7)
     ==> word (val (word (pc + 7):int64) +
               val (word_sx (iword (&(kk + 4) - (&pc + -- &117)):int32):int64)):int64 =
         word_add (word kk) (word 128)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`pc:num`;`7`;`117`;`kk + 4`] RIP_REL_ADDR_FOLD) THEN
  REWRITE_TAC[ARITH_RULE `(kk + 4) + (7 + 117) = kk + 128`] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
  DISCH_THEN(fun th -> DISCH_THEN(fun bound ->
     REWRITE_TAC[MATCH_MP th bound])) THEN
  CONV_TAC WORD_RULE);;

(* ref for capturing the return-address fact at proof time (deref deferred so  *)
(* an eager ASSUME_TAC(!ra_fact) does not bake in TRUTH). *)
let sha256_hw_ra_fact = ref TRUTH;;

(* ---- SysV NOIBT subroutine CORRECT (theorem 1 of 8), WQUAD form. --------- *)
(* Leaf, no stack: prologue = the 1-instr K-base lea; body = CORE_CORRECT      *)
(* (pc+0x07..pc+0x334); epilogue = a bare `ret`.  Internal (native 128-bit     *)
(* SIMD) interface: 2 bytes128 WQUAD reads over the abstract 8-word list H,     *)
(* per-block big-endian WQUAD message reads, 2 WQUAD stores.  The DELIVERED     *)
(* theorem 1 (..._NOIBT_SUBROUTINE_CORRECT, below) is the nohw a..h/bytes32     *)
(* reshape of this, derived mechanically via WQUAD_BYTES32.                     *)
let SHA256_COMPRESS_HW_NOIBT_SUBROUTINE_CORRECT_WQUAD = prove
 (`!pc kk (sptr:int64) (dptr:int64) (H:int32 list) (m:num->int32 list)
     (num_blocks:num) stackpointer returnaddress.
     aligned 16 (word kk:int64) /\
     riprel32_within_bounds (kk + 128) (pc + 7) /\
     0 < num_blocks /\
     val (dptr:int64) + 64 * num_blocks < 2 EXP 64 /\
     nonoverlapping (word pc,825) (sptr,32) /\
     nonoverlapping (word pc,825) (word kk:int64,608) /\
     nonoverlapping (word pc,825) (dptr,64 * num_blocks) /\
     nonoverlapping (stackpointer,8) (sptr,32) /\
     nonoverlapping (word pc,825) (stackpointer,8)
     ==> ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc (kk + 4)) /\
            read RIP s = word pc /\
            read RSP s = stackpointer /\
            read (memory :> bytes64 stackpointer) s = returnaddress /\
            C_ARGUMENTS [sptr; dptr; word num_blocks] s /\
            bytes_loaded s (word kk) K256 /\
            read (memory :> bytes128 sptr) s =
              WQUAD (EL 0 H) (EL 1 H) (EL 2 H) (EL 3 H) /\
            read (memory :> bytes128 (word_add sptr (word 16))) s =
              WQUAD (EL 4 H) (EL 5 H) (EL 6 H) (EL 7 H) /\
            (!j. j < num_blocks
                 ==> read (memory :> bytes128 (word_add dptr (word (64 * j)))) s =
                       WQUAD (word_bytereverse (EL 0 (m j))) (word_bytereverse (EL 1 (m j)))
                             (word_bytereverse (EL 2 (m j))) (word_bytereverse (EL 3 (m j))) /\
                     read (memory :> bytes128 (word_add dptr (word (64 * j + 16)))) s =
                       WQUAD (word_bytereverse (EL 4 (m j))) (word_bytereverse (EL 5 (m j)))
                             (word_bytereverse (EL 6 (m j))) (word_bytereverse (EL 7 (m j))) /\
                     read (memory :> bytes128 (word_add dptr (word (64 * j + 32)))) s =
                       WQUAD (word_bytereverse (EL 8 (m j))) (word_bytereverse (EL 9 (m j)))
                             (word_bytereverse (EL 10 (m j))) (word_bytereverse (EL 11 (m j))) /\
                     read (memory :> bytes128 (word_add dptr (word (64 * j + 48)))) s =
                       WQUAD (word_bytereverse (EL 12 (m j))) (word_bytereverse (EL 13 (m j)))
                             (word_bytereverse (EL 14 (m j))) (word_bytereverse (EL 15 (m j)))))
       (\s. read RIP s = returnaddress /\
            read RSP s = word_add stackpointer (word 8) /\
            read (memory :> bytes128 sptr) s =
              WQUAD (EL 0 (sha256_hash_blocks m H num_blocks))
                    (EL 1 (sha256_hash_blocks m H num_blocks))
                    (EL 2 (sha256_hash_blocks m H num_blocks))
                    (EL 3 (sha256_hash_blocks m H num_blocks)) /\
            read (memory :> bytes128 (word_add sptr (word 16))) s =
              WQUAD (EL 4 (sha256_hash_blocks m H num_blocks))
                    (EL 5 (sha256_hash_blocks m H num_blocks))
                    (EL 6 (sha256_hash_blocks m H num_blocks))
                    (EL 7 (sha256_hash_blocks m H num_blocks)))
       (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [memory :> bytes128 sptr;
                   memory :> bytes128 (word_add sptr (word 16))])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              fst SHA256_COMPRESS_HW_EXEC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SOME_FLAGS] THEN STRIP_TAC THEN
  (* the 6 kptr-relative alignments from aligned 16 (word kk) *)
  MP_TAC SHA256_HW_KPTR_ALIGN THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  (* derive the 16 K WQUAD rows + mask from the s0 bytes_loaded (word kk) K256 *)
  FIRST_ASSUM(fun th ->
    if (try name_of(rand(concl th)) = "K256" with _ -> false)
    then STRIP_ASSUME_TAC(MATCH_MP SHA256_HW_K256_WQUAD_READS
            (REWRITE_RULE[bytes_loaded] th))
    else NO_TAC) THEN
  (* step the K-base lea prologue and fold RCX to kptr *)
  X86_STEPS_TAC SHA256_COMPRESS_HW_EXEC (1--1) THEN
  W(fun (asl,w) ->
     let isra (_,th) =
       let c = concl th in
       (try let _ = find_term (fun t -> try fst(dest_var t)="returnaddress"
                                        with _->false) c in is_eq c
        with _->false) in
     sha256_hw_ra_fact := snd (List.find isra asl); ALL_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SHA256_HW_LEA_FOLD (ASSUME
     `riprel32_within_bounds (kk + 128) (pc + 7)`)]) THEN
  (* apply the core, instantiated at kbase := kk+4, kptr := word_add(word kk)(word 128) *)
  MP_TAC(SPECL
    [`pc:num`; `kk + 4`; `word_add (word kk) (word 128):int64`;
     `sptr:int64`; `dptr:int64`; `H:int32 list`; `m:num->int32 list`;
     `num_blocks:num`]
    (REWRITE_RULE[SOME_FLAGS] SHA256_COMPRESS_HW_CORE_CORRECT)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN (ASM_REWRITE_TAC[] ORELSE NONOVERLAPPING_TAC);
    ALL_TAC] THEN
  X86_BIGSTEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THENL
   [(* core-PRE match: normalize the kptr-relative K/mask addresses to the      *)
    (* bridge's word_add (word kk)(word M) form, then ASM_REWRITE closes it. *)
    REWRITE_TAC[SHA256_HW_KADDR_NORM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* re-derive the return-address fact across the core BIGSTEP (RSP is NOT in   *)
  (* the core frame, and the RA slot is disjoint from sptr, so it is preserved).*)
  SUBGOAL_THEN
   `read (memory :> bytes64 stackpointer) s2 = returnaddress`
  ASSUME_TAC THENL
   [W(fun (asl,w) -> ASSUME_TAC(!sha256_hw_ra_fact)) THEN
    FIRST_X_ASSUM(fun th ->
       if maychange_term(concl th) then MP_TAC th else NO_TAC) THEN
    REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
    REWRITE_TAC[GSYM SEQ_ASSOC] THEN
    PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
    CONV_TAC (TOP_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ASSIGNS_THM] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
    ASSUMPTION_STATE_UPDATE_TAC THEN
    DISCH_THEN(K ALL_TAC) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* step the bare ret and finalize *)
  X86_STEPS_TAC SHA256_COMPRESS_HW_EXEC (3--3) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY MONOTONE_MAYCHANGE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  TRY(CONV_TAC WORD_RULE));;

Printf.printf "S056_SYSV_NOIBT_WQUAD hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_NOIBT_SUBROUTINE_CORRECT_WQUAD))
  (List.length(frees(concl SHA256_COMPRESS_HW_NOIBT_SUBROUTINE_CORRECT_WQUAD)));;

(* ========================================================================== *)
(* Interface reshape: WQUAD/bytes128 <-> nohw a..h/bytes32.                    *)
(* The delivered theorems must mirror the completed nohw sha256_compress ones  *)
(* (a..h dword state, per-dword byte-reversed message hyp, 8 bytes32 output    *)
(* reads) modulo the _HW naming (orchestrator ruling 2026-07-09, per BRIEF).   *)
(* WQUAD_BYTES32 is the atomic bridge: a bytes128 WQUAD read is exactly its 4  *)
(* consecutive bytes32 dword reads (READ_MEMORY_BYTESIZED_UNSPLIT decomposes   *)
(* bytes128 -> 2 bytes64 -> 4 bytes32 as word_subword projections; WQUAD_SUB64 *)
(* collapses the nested subwords of a WQUAD to its 4 dwords).                   *)
(* ------------------------------------------------------------------------- *)

let HW_UNSPLIT128 = CONJUNCT1(CONJUNCT2 READ_MEMORY_BYTESIZED_UNSPLIT);;
let HW_UNSPLIT64  = CONJUNCT1(CONJUNCT2(CONJUNCT2 READ_MEMORY_BYTESIZED_UNSPLIT));;

let WQUAD_SUB64 = prove
 (`word_subword (word_subword (WQUAD a b c d) (0,64):int64) (0,32):int32 = a /\
   word_subword (word_subword (WQUAD a b c d) (0,64):int64) (32,32):int32 = b /\
   word_subword (word_subword (WQUAD a b c d) (64,64):int64) (0,32):int32 = c /\
   word_subword (word_subword (WQUAD a b c d) (64,64):int64) (32,32):int32 = d`,
  REWRITE_TAC[WQUAD] THEN CONV_TAC WORD_BLAST);;

let WQUAD_BYTES32 = prove
 (`!(x:int64) s a b c d.
     read (memory :> bytes128 x) s = WQUAD a b c d <=>
     read (memory :> bytes32 x) s = a /\
     read (memory :> bytes32 (word_add x (word 4))) s = b /\
     read (memory :> bytes32 (word_add x (word 8))) s = c /\
     read (memory :> bytes32 (word_add x (word 12))) s = d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HW_UNSPLIT128; HW_UNSPLIT64] THEN
  REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WQUAD_SUB64] THEN CONV_TAC CONJ_ACI_RULE);;

let HW_EL8 = prove
 (`EL 0 [a;b;c;d;e;f;g;h:int32] = a /\ EL 1 [a;b;c;d;e;f;g;h] = b /\
   EL 2 [a;b;c;d;e;f;g;h] = c /\ EL 3 [a;b;c;d;e;f;g;h] = d /\
   EL 4 [a;b;c;d;e;f;g;h] = e /\ EL 5 [a;b;c;d;e;f;g;h] = f /\
   EL 6 [a;b;c;d;e;f;g;h] = g /\ EL 7 [a;b;c;d;e;f;g;h] = h`,
  CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;

(* the state/output write frame: 2 bytes128 WQUAD stores over statep are        *)
(* subsumed by the single 32-byte region bytes(statep,32) -- the honest SIMD    *)
(* frame (a 128-bit store is NOT element-wise subsumed by 4 separate bytes32    *)
(* writes, so we present the region form, as aes_xts_encrypt does).             *)
let HW_MEM_TAIL_SUB = prove
 (`(MAYCHANGE [memory :> bytes128 (statep:int64);
               memory :> bytes128 (word_add statep (word 16))]) subsumed
   (MAYCHANGE [memory :> bytes(statep,32)])`,
  SUBSUMED_MAYCHANGE_TAC);;

let HW_FRAME_SUBSUMED = prove
 (`!statep:int64.
     (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes128 statep;
                 memory :> bytes128 (word_add statep (word 16))]) subsumed
     (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(statep,32)])`,
  GEN_TAC THEN REWRITE_TAC[GSYM SEQ_ASSOC] THEN
  MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL] THEN
  MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL] THEN
  MATCH_ACCEPT_TAC HW_MEM_TAIL_SUB);;

(* from the nohw per-dword message hyp in the assumptions, ASSUME the reduced   *)
(* read bytes32(dataptr + word(64*j + 4*n)) = brev(EL n (m_fn j)) fact.         *)
let hw_dword_fact n =
  FIRST_ASSUM(fun th ->
    if free_in `word_bytereverse:int32->int32` (concl th)
    then
      let sp = SPECL [`j:num`; mk_small_numeral n] th in
      ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)
        (MP sp (CONJ (ASSUME `j < num_blocks`)
                     (ARITH_RULE(mk_comb(mk_comb(`(<):num->num->bool`,
                        mk_small_numeral n),`16`))))))
    else NO_TAC);;

(* ---- SysV NOIBT subroutine CORRECT (theorem 1 of 8), nohw interface. ------ *)
let SHA256_COMPRESS_HW_NOIBT_SUBROUTINE_CORRECT = prove
 (`!pc kk (statep:int64) (dataptr:int64) (num_blocks:num)
     a b c d e f g h (m_fn:num->int32 list) stackpointer returnaddress.
     aligned 16 (word kk:int64) /\
     riprel32_within_bounds (kk + 128) (pc + 7) /\
     0 < num_blocks /\
     val (dataptr:int64) + 64 * num_blocks < 2 EXP 64 /\
     nonoverlapping (word pc,825) (statep,32) /\
     nonoverlapping (word pc,825) (word kk:int64,608) /\
     nonoverlapping (word pc,825) (dataptr,64 * num_blocks) /\
     nonoverlapping (stackpointer,8) (statep,32) /\
     nonoverlapping (word pc,825) (stackpointer,8)
     ==> ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc (kk + 4)) /\
            read RIP s = word pc /\
            read RSP s = stackpointer /\
            read (memory :> bytes64 stackpointer) s = returnaddress /\
            C_ARGUMENTS [statep; dataptr; word num_blocks] s /\
            bytes_loaded s (word kk) K256 /\
            read (memory :> bytes32 statep) s = (a:int32) /\
            read (memory :> bytes32 (word_add statep (word 4))) s = (b:int32) /\
            read (memory :> bytes32 (word_add statep (word 8))) s = (c:int32) /\
            read (memory :> bytes32 (word_add statep (word 12))) s = (d:int32) /\
            read (memory :> bytes32 (word_add statep (word 16))) s = (e:int32) /\
            read (memory :> bytes32 (word_add statep (word 20))) s = (f:int32) /\
            read (memory :> bytes32 (word_add statep (word 24))) s = (g:int32) /\
            read (memory :> bytes32 (word_add statep (word 28))) s = (h:int32) /\
            (!i' j. i' < num_blocks /\ j < 16
                    ==> read (memory :> bytes32
                          (word_add dataptr (word (64*i' + 4*j)))) s =
                        word_bytereverse (EL j (m_fn i'):int32)))
       (\s. read RIP s = returnaddress /\
            read RSP s = word_add stackpointer (word 8) /\
            read (memory :> bytes32 statep) s =
              EL 0 (sha256_hash_blocks m_fn [a;b;c;d;e;f;g;h] num_blocks) /\
            read (memory :> bytes32 (word_add statep (word 4))) s =
              EL 1 (sha256_hash_blocks m_fn [a;b;c;d;e;f;g;h] num_blocks) /\
            read (memory :> bytes32 (word_add statep (word 8))) s =
              EL 2 (sha256_hash_blocks m_fn [a;b;c;d;e;f;g;h] num_blocks) /\
            read (memory :> bytes32 (word_add statep (word 12))) s =
              EL 3 (sha256_hash_blocks m_fn [a;b;c;d;e;f;g;h] num_blocks) /\
            read (memory :> bytes32 (word_add statep (word 16))) s =
              EL 4 (sha256_hash_blocks m_fn [a;b;c;d;e;f;g;h] num_blocks) /\
            read (memory :> bytes32 (word_add statep (word 20))) s =
              EL 5 (sha256_hash_blocks m_fn [a;b;c;d;e;f;g;h] num_blocks) /\
            read (memory :> bytes32 (word_add statep (word 24))) s =
              EL 6 (sha256_hash_blocks m_fn [a;b;c;d;e;f;g;h] num_blocks) /\
            read (memory :> bytes32 (word_add statep (word 28))) s =
              EL 7 (sha256_hash_blocks m_fn [a;b;c;d;e;f;g;h] num_blocks))
       (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [memory :> bytes(statep,32)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* instantiate the WQUAD theorem at H:=[a..h], m:=m_fn, sptr:=statep, then    *)
  (* reframe to the bytes-region frame.                                         *)
  MP_TAC(SPECL
    [`pc:num`;`kk:num`;`statep:int64`;`dataptr:int64`;
     `[a;b;c;d;e;f;g;h]:int32 list`;`m_fn:num->int32 list`;
     `num_blocks:num`;`stackpointer:int64`;`returnaddress:int64`]
    SHA256_COMPRESS_HW_NOIBT_SUBROUTINE_CORRECT_WQUAD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun wthm ->
    let wthm2 = MATCH_MP ENSURES_FRAME_SUBSUMED
                  (CONJ (SPEC `statep:int64` HW_FRAME_SUBSUMED) wthm) in
    MATCH_MP_TAC ENSURES_PREPOSTCONDITION_THM THEN
    EXISTS_TAC (rand(rator(rator(concl wthm2)))) THEN
    EXISTS_TAC (rand(rator(concl wthm2))) THEN
    REPEAT CONJ_TAC THENL
     [(* P' x ==> P x : nohw dwords ==> WQUAD reads *)
      GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
      REWRITE_TAC[HW_EL8; WQUAD_BYTES32] THEN
      REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REPEAT CONJ_TAC THEN
      TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      REWRITE_TAC[MSG_ADDR] THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY hw_dword_fact [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
      ASM_REWRITE_TAC[];
      (* Q x ==> Q' x : WQUAD post ==> nohw dwords *)
      GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[WQUAD_BYTES32; WORD_ADD_ASSOC_CONSTS]) THEN
      RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
      ASM_REWRITE_TAC[];
      (* ensures step P Q C : the reframed WQUAD theorem *)
      MATCH_ACCEPT_TAC wthm2]));;

Printf.printf "S057_SYSV_NOIBT hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_NOIBT_SUBROUTINE_CORRECT))
  (List.length(frees(concl SHA256_COMPRESS_HW_NOIBT_SUBROUTINE_CORRECT)));;

(* ========================================================================== *)
(* IBT-lift building blocks (theorem 2/8, hand-rolled — the standard           *)
(* ADD_IBT_RULE ~bridge REJECTS this code: the K-lea's NEGATIVE riprel (-117)  *)
(* means define_trimmed leaves it UNSHIFTED, so the bridge is `tmc pc` NOT     *)
(* `tmc (pc+4)`, and ADD_IBT_RULE is hard-wired to the +4 shape).              *)
(* ------------------------------------------------------------------------- *)

(* mc pc kk = APPEND [endbr64] (tmc pc kk).  Note the RHS is tmc **pc** (same  *)
(* pc as mc), not tmc (pc+4): the negative riprel is unshifted by trimming.    *)
let SHA256_COMPRESS_HW_MC_BRIDGE = prove
 (`!pc kk. sha256_compress_hw_mc pc kk =
     APPEND [word 0xf3:byte; word 0x0f; word 0x1e; word 0xfa]
            (sha256_compress_hw_tmc pc kk)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[sha256_compress_hw_mc; sha256_compress_hw_tmc; APPEND] THEN
  REWRITE_TAC[]);;

(* Shift-invariance of the trimmed image: the K-lea disp is (kk - pc + 117),   *)
(* invariant under (pc,kk) -> (pc+4,kk+4).  This is what lets the IBT hand-roll *)
(* MP the NOIBT wrapper at pc:=pc+4, kk:=kk (body tmc(pc+4)(kk+4) = tmc pc kk). *)
let SHA256_COMPRESS_HW_TMC_SHIFT = prove
 (`!pc kk. sha256_compress_hw_tmc (pc + 4) (kk + 4) =
           sha256_compress_hw_tmc pc kk`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sha256_compress_hw_tmc] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
  REWRITE_TAC[INT_ARITH `(&kk + &4) - ((&pc + &4) + -- &117) =
                         &kk - (&pc + -- &117):int`]);;

Printf.printf "S057_IBT_BLOCKS ok\n%!";;

(* ========================================================================== *)
(* SysV IBT/endbr64 subroutine CORRECT (theorem 2 of 8).                       *)
(*                                                                             *)
(* The stock `ADD_IBT_RULE ~bridge:...` cannot lift this routine: its `adjust` *)
(* function bumps every `pc + n` / `(word pc, n)` by 4 AND rewrites the code   *)
(* constant tmc -> mc, but leaves the K-base argument `kk + 4` untouched --    *)
(* yielding code `mc pc (kk+4)` while K256 stays at `word kk`.  Because the    *)
(* K-lea has a NEGATIVE riprel (-117) that define_trimmed leaves UNSHIFTED,    *)
(* `mc pc (kk+4)` targets kk+132 whereas kptr = kk+128 -- a geometrically      *)
(* inconsistent, unprovable goal.  So we HAND-ROLL the lift with the correct   *)
(* geometry ("V1"): code `mc pc kk`, K256 @ `word kk`, everything in the same  *)
(* `kk` as the NOIBT theorem.  mc's lea sits at pc+11 (after the 4-byte endbr) *)
(* with disp (kk - pc + 117), so its target is pc+11 + (kk-pc+117) = kk+128 =  *)
(* kptr -- consistent.  The proof mirrors ADD_IBT_TAC_PARAMETRIZED but MPs the *)
(* NOIBT wrapper at (pc+4, kk): the inner body `tmc pc kk` (from MC_BRIDGE) is *)
(* reconciled with NOIBT's `tmc (pc+4) (kk+4)` via SHA256_COMPRESS_HW_TMC_SHIFT.*)
(* Only tmc->mc, 825->829, and (pc+7)->(pc+11) change vs the NOIBT statement.  *)
(* ------------------------------------------------------------------------- *)
let SHA256_COMPRESS_HW_SUBROUTINE_CORRECT = prove
 (`!pc kk (statep:int64) (dataptr:int64) (num_blocks:num)
     a b c d e f g h (m_fn:num->int32 list) stackpointer returnaddress.
     aligned 16 (word kk:int64) /\
     riprel32_within_bounds (kk + 128) (pc + 11) /\
     0 < num_blocks /\
     val (dataptr:int64) + 64 * num_blocks < 2 EXP 64 /\
     nonoverlapping (word pc,829) (statep,32) /\
     nonoverlapping (word pc,829) (word kk:int64,608) /\
     nonoverlapping (word pc,829) (dataptr,64 * num_blocks) /\
     nonoverlapping (stackpointer,8) (statep,32) /\
     nonoverlapping (word pc,829) (stackpointer,8)
     ==> ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_mc pc kk) /\
            read RIP s = word pc /\
            read RSP s = stackpointer /\
            read (memory :> bytes64 stackpointer) s = returnaddress /\
            C_ARGUMENTS [statep; dataptr; word num_blocks] s /\
            bytes_loaded s (word kk) K256 /\
            read (memory :> bytes32 statep) s = (a:int32) /\
            read (memory :> bytes32 (word_add statep (word 4))) s = (b:int32) /\
            read (memory :> bytes32 (word_add statep (word 8))) s = (c:int32) /\
            read (memory :> bytes32 (word_add statep (word 12))) s = (d:int32) /\
            read (memory :> bytes32 (word_add statep (word 16))) s = (e:int32) /\
            read (memory :> bytes32 (word_add statep (word 20))) s = (f:int32) /\
            read (memory :> bytes32 (word_add statep (word 24))) s = (g:int32) /\
            read (memory :> bytes32 (word_add statep (word 28))) s = (h:int32) /\
            (!i' j. i' < num_blocks /\ j < 16
                    ==> read (memory :> bytes32
                          (word_add dataptr (word (64*i' + 4*j)))) s =
                        word_bytereverse (EL j (m_fn i'):int32)))
       (\s. read RIP s = returnaddress /\
            read RSP s = word_add stackpointer (word 8) /\
            read (memory :> bytes32 statep) s =
              EL 0 (sha256_hash_blocks m_fn [a;b;c;d;e;f;g;h] num_blocks) /\
            read (memory :> bytes32 (word_add statep (word 4))) s =
              EL 1 (sha256_hash_blocks m_fn [a;b;c;d;e;f;g;h] num_blocks) /\
            read (memory :> bytes32 (word_add statep (word 8))) s =
              EL 2 (sha256_hash_blocks m_fn [a;b;c;d;e;f;g;h] num_blocks) /\
            read (memory :> bytes32 (word_add statep (word 12))) s =
              EL 3 (sha256_hash_blocks m_fn [a;b;c;d;e;f;g;h] num_blocks) /\
            read (memory :> bytes32 (word_add statep (word 16))) s =
              EL 4 (sha256_hash_blocks m_fn [a;b;c;d;e;f;g;h] num_blocks) /\
            read (memory :> bytes32 (word_add statep (word 20))) s =
              EL 5 (sha256_hash_blocks m_fn [a;b;c;d;e;f;g;h] num_blocks) /\
            read (memory :> bytes32 (word_add statep (word 24))) s =
              EL 6 (sha256_hash_blocks m_fn [a;b;c;d;e;f;g;h] num_blocks) /\
            read (memory :> bytes32 (word_add statep (word 28))) s =
              EL 7 (sha256_hash_blocks m_fn [a;b;c;d;e;f;g;h] num_blocks))
       (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [memory :> bytes(statep,32)])`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SHA256_COMPRESS_HW_MC_BRIDGE] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; SOME_FLAGS;
              C_ARGUMENTS; C_RETURN; WINDOWS_C_ARGUMENTS;
              WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN
  IBT_WRAP_TAC
   (W (fun (asl,w) ->
      let avs,_ =
        strip_forall (concl SHA256_COMPRESS_HW_NOIBT_SUBROUTINE_CORRECT) in
      let new_avs = map (fun v ->
        if is_var v && name_of v = "pc" then mk_binary "+" (v,`4`) else v) avs in
      MP_TAC (REWRITE_RULE[C_ARGUMENTS; C_RETURN; WINDOWS_C_ARGUMENTS;
                            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                            WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                            SOME_FLAGS; SHA256_COMPRESS_HW_TMC_SHIFT]
              (SPECL new_avs SHA256_COMPRESS_HW_NOIBT_SUBROUTINE_CORRECT)) THEN
      CONV_TAC(ONCE_DEPTH_CONV
        (REWR_CONV(ARITH_RULE `(pc + 4) + n:num = pc + (n + 4)`) THENC
         RAND_CONV NUM_ADD_CONV)) THEN
      REWRITE_TAC[
        WORD_RULE `word(pc+4):int64 = word_add (word pc) (word 4)`] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
      REPEAT CONJ_TAC THEN
      TRY (FIRST_X_ASSUM ACCEPT_TAC) THEN
      NONOVERLAPPING_TAC)));;

Printf.printf "S058_SYSV_IBT hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_SUBROUTINE_CORRECT))
  (List.length(frees(concl SHA256_COMPRESS_HW_SUBROUTINE_CORRECT)));;

(* ========================================================================= *)
(* Phase 9 -- core SAFE (events-only constant-time + memory safety).         *)
(*                                                                           *)
(* The events analogue of CORE_CORRECT (same UP2 loop geometry pc+0x07 ->    *)
(* pc+0x334, loop-top pc+0x38, jne back-edge folded at pc+0x30c fall-through  *)
(* pc+0x312).  A SAFE postcondition carries only an events trace + inbounds   *)
(* facts (no algebraic spec value), so the SHA-NI body flat-steps with NO     *)
(* term growth -- the 24KB-per-step blowup that forced the per-round cuts of  *)
(* CORE_CORRECT is a value-tracking artifact; in events mode the XMM/YMM      *)
(* values live in MAYCHANGE and are never reasoned about (measured s059: the  *)
(* 170-instr body steps in ~15s flat).  So the whole 170-instruction body     *)
(* (incl. the folded jne) is ONE continuous X86_STEPS_TAC segment -- the SAFE *)
(* carve-out to the "cut above ~30 instrs" rule.                             *)
(*                                                                           *)
(* Loop = dec rdx; jne (ZF/counter back-edge, same as CORE_CORRECT) NOT the   *)
(* scalar nohw cmp;jb, so the CF bridge (CFLT_IFF) is replaced by the ZF/     *)
(* counter reconciliation (SHA256_HW_RDX_STEP/RSI_STEP/ZF_EXIT), and there is  *)
(* no cmpb sentinel and no C8 stepper.  Leaf, no stack: no stackpointer in     *)
(* the events args, read/write sets, or invariant.                           *)
(*                                                                           *)
(* Read set (superset of the write set): [statep,32; dataptr,64*nb;           *)
(* word kk,608].  Write set: [statep,32].  The K base register RCX = kptr =   *)
(* kk+128, so the stepper emits K accesses as word_add (kk+128) (word DISP);   *)
(* the read region shares the clean base `word kk` and the accessed addresses *)
(* fold to word_add (word kk) (word M) via SHA256_HW_KADDR_NORM before the     *)
(* memaccess_inbounds discharge.                                             *)
(* ------------------------------------------------------------------------- *)

(* f_events skeleton: epilogue ++ (loop iterated nb) ++ prologue. *)
let sha256_hw_safe_f_events_shape =
  `\(dptr:int64) (sptr:int64) (num_blocks:num) (kk:num) (pc:num).
    APPEND
      (f_ev_epil dptr sptr num_blocks kk pc)
      (APPEND
        (ENUMERATEL num_blocks (\i.
          f_ev_loop dptr sptr num_blocks kk pc i))
        (f_ev_prol dptr sptr num_blocks kk pc))
  :(uarch_event)list`;;

let sha256_hw_core_safe_concl =
  let pre =
   `\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc kbase) /\
        read RIP s = word (pc + 0x07) /\
        read RCX s = word_add (word kk) (word 128) /\
        read RDI s = sptr /\
        read RSI s = dptr /\
        read RDX s = word num_blocks /\
        read events s = e` in
  let post =
   `\s. read RIP s = word (pc + 0x334) /\
        (exists e2.
           read events s = APPEND e2 e /\
           e2 = f_events dptr sptr num_blocks kk pc /\
           memaccess_inbounds e2
             [sptr:int64,32; dptr:int64,64*num_blocks; word kk:int64,608]
             [sptr:int64,32])` in
  let frame =
   `MAYCHANGE [RIP; RSI; RDX] ,,
    MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM5_SSE;
               YMM6_SSE; YMM7_SSE; YMM8_SSE; YMM9_SSE; YMM10_SSE] ,,
    MAYCHANGE [memory :> bytes128 sptr;
               memory :> bytes128 (word_add sptr (word 16))] ,,
    MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]` in
  mk_exists(`f_events:int64->int64->num->num->num->(uarch_event)list`,
    list_mk_forall(
      [`pc:num`;`kbase:num`;`kk:num`;`sptr:int64`;`dptr:int64`;
       `num_blocks:num`;`e:(uarch_event)list`],
      itlist (curry mk_imp)
        [`aligned 16 (word kk:int64)`;
         `0 < num_blocks`;
         `val (dptr:int64) + 64 * num_blocks < 2 EXP 64`;
         `nonoverlapping (word pc,825) (sptr:int64,32)`]
        (list_mk_comb(`ensures x86`, [pre; post; frame]))));;

(* loop invariant @ pc+0x38 for iteration i: address regs only (the events-   *)
(* exists is auto-appended by ENSURES_EVENTS_WHILE_UP2_TAC).                   *)
let sha256_hw_safe_loop_inv =
  `\i s. read RCX s = word_add (word kk) (word 128):int64 /\
         read RDI s = sptr /\
         read RSI s = word_add dptr (word (64*i)) /\
         read RDX s = word (num_blocks - i)`;;

let SHA256_COMPRESS_HW_CORE_SAFE = prove
 (sha256_hw_core_safe_concl,
  CONCRETIZE_F_EVENTS_TAC sha256_hw_safe_f_events_shape THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `num_blocks:num` `pc + 0x38` `pc + 0x312`
    sha256_hw_safe_loop_inv THEN
  REPEAT CONJ_TAC THENL [
    (* ---- arith: ~(num_blocks = 0) ---- *)
    ASM_ARITH_TAC;
    (* ---- init: entry-repack pc+0x07 -> pc+0x38 (10 instrs) -> loopinv 0.    *)
    (* Derive the 6 kptr-relative alignments (movdqa spin guard) from           *)
    (* aligned 16 (word kk); step; peel the address-reg conjuncts; discharge.   *)
    MP_TAC SHA256_HW_KPTR_ALIGN THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC SHA256_COMPRESS_HW_EXEC (1--10) THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; ADD_CLAUSES; SUB_0] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT (CONJ_TAC THENL
     [ (CONV_TAC WORD_RULE ORELSE ASM_REWRITE_TAC[]); ALL_TAC ]) THEN
    SAFE_META_EXISTS_TAC allowed_vars_e THEN
    CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
    W (fun (asl,w) ->
      (if is_conj w then (CONJ_TAC THENL [ FULL_UNIFY_F_EVENTS_TAC; ALL_TAC ])
       else ALL_TAC) THEN
      REWRITE_TAC[SHA256_HW_KADDR_NORM] THEN
      DISCHARGE_MEMACCESS_INBOUNDS_TAC);
    (* ---- body: pc+0x38 loopinv i -> (if i+1<nb then pc+0x38 else pc+0x312)   *)
    (* loopinv(i+1).  170 flat steps incl the jne.  ZF-counter reconciliation:  *)
    (* RIP via ZF_EXIT + COND_CASES, RSI via RSI_STEP, RDX via RDX_STEP.         *)
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `num_blocks < 2 EXP 64` ASSUME_TAC THENL
     [TRANS_TAC LET_TRANS `val (dptr:int64) + 64 * num_blocks` THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    MP_TAC SHA256_HW_KPTR_ALIGN THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC SHA256_COMPRESS_HW_EXEC (1--170) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT (CONJ_TAC THENL
     [ (ASM_SIMP_TAC[SHA256_HW_RSI_STEP; SHA256_HW_RDX_STEP] THEN NO_TAC) ORELSE
       (CONV_TAC WORD_RULE) ORELSE
       (ASM_SIMP_TAC[SHA256_HW_ZF_EXIT] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[]) ORELSE
       ASM_REWRITE_TAC[]; ALL_TAC ]) THEN
    SAFE_META_EXISTS_TAC allowed_vars_e THEN
    CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
    W (fun (asl,w) ->
      (if is_conj w then (CONJ_TAC THENL [ FULL_UNIFY_F_EVENTS_TAC; ALL_TAC ])
       else ALL_TAC) THEN
      REWRITE_TAC[SHA256_HW_KADDR_NORM] THEN
      DISCHARGE_MEMACCESS_INBOUNDS_TAC);
    (* ---- exit: pc+0x312 loopinv nb -> pc+0x334 (7 instrs). ---- *)
    ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC SHA256_COMPRESS_HW_EXEC (1--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SAFE_META_EXISTS_TAC allowed_vars_e THEN
    CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
    W (fun (asl,w) ->
      (if is_conj w then (CONJ_TAC THENL [ FULL_UNIFY_F_EVENTS_TAC; ALL_TAC ])
       else ALL_TAC) THEN
      REWRITE_TAC[SHA256_HW_KADDR_NORM] THEN
      DISCHARGE_MEMACCESS_INBOUNDS_TAC) ]);;

Printf.printf "S059_CORE_SAFE hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_CORE_SAFE))
  (List.length(frees(concl SHA256_COMPRESS_HW_CORE_SAFE)));;

(* ========================================================================= *)
(* Phase 9 -- SysV NOIBT subroutine SAFE (theorem 5 of 8).                   *)
(*                                                                           *)
(* Leaf, no stack: prologue = the 1-instr K-base lea; body = CORE_SAFE       *)
(* (pc+0x07..pc+0x334); epilogue = a bare `ret`.  Structurally the SAFE      *)
(* analogue of SHA256_COMPRESS_HW_NOIBT_SUBROUTINE_CORRECT (thm 1): the       *)
(* stock X86_PROMOTE_RETURN_NOSTACK_TAC does not apply (the lea prologue      *)
(* precedes the core), so we HAND-ROLL -- step the lea, fold RCX = kptr via   *)
(* SHA256_HW_LEA_FOLD, MP the core SAFE, X86_BIGSTEP over the core, re-derive *)
(* the return address across the core (RSP not in the core frame + RA slot    *)
(* disjoint from statep), step the bare ret, then DISCHARGE_SAFETY_PROPERTY.  *)
(* Wrapper events e2 = ret trace ++ core f_events, threaded as a metavar via   *)
(* ASSUME_CALLEE_SAFETY_TAC + META_EXISTS_TAC (resolved by DISCHARGE).        *)
(* Read set = [statep,32; dataptr,64*nb; word kk,608; stackpointer,8]         *)
(* (the RA read at [rsp]) SUPERSET write set [statep,32; stackpointer,0]      *)
(* (leaf reads its RA but writes no stack; statep as the accepted region      *)
(* frame, cf. thms 1-2).                                                      *)
(* ------------------------------------------------------------------------- *)

(* ref for capturing the s1 events trace to feed the core SAFE's e argument.  *)
let sha256_hw_e_wrap = ref `e:(uarch_event)list`;;

let SHA256_COMPRESS_HW_NOIBT_SUBROUTINE_SAFE = prove
 (`exists f_events.
    forall e pc kk (statep:int64) (dataptr:int64) (num_blocks:num)
           stackpointer returnaddress.
        aligned 16 (word kk:int64) /\
        riprel32_within_bounds (kk + 128) (pc + 7) /\
        0 < num_blocks /\
        val (dataptr:int64) + 64 * num_blocks < 2 EXP 64 /\
        nonoverlapping (word pc,825) (statep,32) /\
        nonoverlapping (word pc,825) (word kk:int64,608) /\
        nonoverlapping (word pc,825) (dataptr,64 * num_blocks) /\
        nonoverlapping (stackpointer,8) (statep,32) /\
        nonoverlapping (word pc,825) (stackpointer,8)
        ==> ensures x86
            (\s. bytes_loaded s (word pc) (sha256_compress_hw_tmc pc (kk + 4)) /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [statep; dataptr; word num_blocks] s /\
                 bytes_loaded s (word kk) K256 /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events dataptr statep num_blocks kk pc
                             stackpointer returnaddress /\
                      memaccess_inbounds e2
                        [statep:int64,32; dataptr:int64,64 * num_blocks;
                         word kk:int64,608; stackpointer:int64,8]
                        [statep:int64,32; stackpointer:int64,0]))
            (MAYCHANGE [RSP] ,,
             MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(statep,32)] ,,
             MAYCHANGE [events])`,
  REWRITE_TAC[fst SHA256_COMPRESS_HW_EXEC] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS] THEN
  ASSUME_CALLEE_SAFETY_TAC SHA256_COMPRESS_HW_CORE_SAFE "HCORE" THEN
  META_EXISTS_TAC THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  (* capture the RA fact for re-derivation across the core BIGSTEP *)
  W(fun (asl,w) ->
     let isra (_,th) =
       let c = concl th in
       (try let _ = find_term (fun t -> try fst(dest_var t)="returnaddress"
                                        with _->false) c in is_eq c
        with _->false) in
     sha256_hw_ra_fact := snd (List.find isra asl); ALL_TAC) THEN
  (* step the K-base lea prologue and fold RCX to kptr = kk+128 *)
  X86_STEPS_TAC SHA256_COMPRESS_HW_EXEC (1--1) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SHA256_HW_LEA_FOLD (ASSUME
     `riprel32_within_bounds (kk + 128) (pc + 7)`)]) THEN
  (* capture the s1 events trace to feed the core SAFE's e argument *)
  W(fun (asl,w) ->
     let _,th = find (fun (_,th) ->
        let c = concl th in
        is_eq c && string_of_term(lhand c) = "read events s1") asl in
     sha256_hw_e_wrap := rhs(concl th); ALL_TAC) THEN
  (* MP the core SAFE (HCORE) at the wrapper instantiation *)
  W(fun (asl,w) ->
    let _,hcore = find (fun (nm,_) -> nm="HCORE") asl in
    let specth = SPECL
      [ `pc:num`; `kk + 4`; `kk:num`; `statep:int64`; `dataptr:int64`;
        `num_blocks:num`; !sha256_hw_e_wrap ] hcore in
    MP_TAC (REWRITE_RULE[IMP_IMP] specth)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN (ASM_REWRITE_TAC[] ORELSE NONOVERLAPPING_TAC);
    ALL_TAC] THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  X86_BIGSTEP_TAC SHA256_COMPRESS_HW_EXEC "s2" THEN
  (* re-derive the return-address fact across the core BIGSTEP *)
  SUBGOAL_THEN `read (memory :> bytes64 stackpointer) s2 = returnaddress`
  ASSUME_TAC THENL
   [W(fun (asl,w) -> ASSUME_TAC(!sha256_hw_ra_fact)) THEN
    FIRST_X_ASSUM(fun th ->
       if maychange_term(concl th) then MP_TAC th else NO_TAC) THEN
    REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
    REWRITE_TAC[GSYM SEQ_ASSOC] THEN
    PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
    CONV_TAC (TOP_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ASSIGNS_THM] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
    ASSUMPTION_STATE_UPDATE_TAC THEN
    DISCH_THEN(K ALL_TAC) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* step the bare ret and discharge the safety property *)
  X86_STEPS_TAC SHA256_COMPRESS_HW_EXEC (3--3) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

Printf.printf "S059_SYSV_NOIBT_SAFE hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_NOIBT_SUBROUTINE_SAFE))
  (List.length(frees(concl SHA256_COMPRESS_HW_NOIBT_SUBROUTINE_SAFE)));;

(* ========================================================================= *)
(* Phase 9 -- SysV IBT/endbr64 subroutine SAFE (theorem 6 of 8).             *)
(*                                                                           *)
(* The SAFE analogue of SHA256_COMPRESS_HW_SUBROUTINE_CORRECT (thm 2): the    *)
(* stock ADD_IBT_RULE ~bridge REJECTS this routine (its adjust leaves the     *)
(* K-base kk+4 while bumping offsets, and the NEGATIVE riprel -117 is left    *)
(* unshifted, so mc pc (kk+4) targets kk+132 != kptr=kk+128 -- verified: the  *)
(* one-liner throws Failure "tryfind").  So we HAND-ROLL exactly as thm 2,    *)
(* mirroring ADD_IBT_TAC_PARAMETRIZED (which is SAFE-aware -- ADD_IBT_OPEN_    *)
(* EXISTS handles the `exists f_events` head, feeding a witnessed forall       *)
(* th_inner) but injecting SHA256_COMPRESS_HW_TMC_SHIFT into the MP'd          *)
(* th_inner's REWRITE list so the inner body tmc(pc+4)(kk+4) folds to the      *)
(* MC_BRIDGE body tmc pc kk.  Only tmc->mc, 825->829, (pc+7)->(pc+11) change.  *)
(* ------------------------------------------------------------------------- *)
let SHA256_COMPRESS_HW_SUBROUTINE_SAFE = prove
 (`exists f_events.
    forall e pc kk (statep:int64) (dataptr:int64) (num_blocks:num)
           stackpointer returnaddress.
        aligned 16 (word kk:int64) /\
        riprel32_within_bounds (kk + 128) (pc + 11) /\
        0 < num_blocks /\
        val (dataptr:int64) + 64 * num_blocks < 2 EXP 64 /\
        nonoverlapping (word pc,829) (statep,32) /\
        nonoverlapping (word pc,829) (word kk:int64,608) /\
        nonoverlapping (word pc,829) (dataptr,64 * num_blocks) /\
        nonoverlapping (stackpointer,8) (statep,32) /\
        nonoverlapping (word pc,829) (stackpointer,8)
        ==> ensures x86
            (\s. bytes_loaded s (word pc) (sha256_compress_hw_mc pc kk) /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [statep; dataptr; word num_blocks] s /\
                 bytes_loaded s (word kk) K256 /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events dataptr statep num_blocks kk pc
                             stackpointer returnaddress /\
                      memaccess_inbounds e2
                        [statep:int64,32; dataptr:int64,64 * num_blocks;
                         word kk:int64,608; stackpointer:int64,8]
                        [statep:int64,32; stackpointer:int64,0]))
            (MAYCHANGE [RSP] ,,
             MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(statep,32)] ,,
             MAYCHANGE [events])`,
  REWRITE_TAC[SHA256_COMPRESS_HW_MC_BRIDGE] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; SOME_FLAGS;
              C_ARGUMENTS; C_RETURN; WINDOWS_C_ARGUMENTS;
              WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ADD_IBT_OPEN_EXISTS SHA256_COMPRESS_HW_NOIBT_SUBROUTINE_SAFE
   (fun th_inner ->
    REPEAT GEN_TAC THEN
    REWRITE_TAC[SHA256_COMPRESS_HW_MC_BRIDGE] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; SOME_FLAGS;
                C_ARGUMENTS; C_RETURN; WINDOWS_C_ARGUMENTS;
                WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT STRIP_TAC THEN
    IBT_WRAP_TAC
     (W (fun (asl,w) ->
        let avs,_ = strip_forall (concl th_inner) in
        let new_avs = map (fun v ->
          if is_var v && name_of v = "pc" then mk_binary "+" (v,`4`) else v)
          avs in
        MP_TAC (REWRITE_RULE[C_ARGUMENTS; C_RETURN; WINDOWS_C_ARGUMENTS;
                              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                              WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                              SOME_FLAGS; SHA256_COMPRESS_HW_TMC_SHIFT]
                (SPECL new_avs th_inner)) THEN
        CONV_TAC(ONCE_DEPTH_CONV
          (REWR_CONV(ARITH_RULE `(pc + 4) + n:num = pc + (n + 4)`) THENC
           RAND_CONV NUM_ADD_CONV)) THEN
        REWRITE_TAC[
          WORD_RULE `word(pc+4):int64 = word_add (word pc) (word 4)`] THEN
        DISCH_THEN MATCH_MP_TAC THEN
        POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
        REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
        REPEAT CONJ_TAC THEN
        TRY (FIRST_X_ASSUM ACCEPT_TAC) THEN
        NONOVERLAPPING_TAC))));;

Printf.printf "S059_SYSV_IBT_SAFE hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_SUBROUTINE_SAFE))
  (List.length(frees(concl SHA256_COMPRESS_HW_SUBROUTINE_SAFE)));;

(* ========================================================================== *)
(* Phase 8 — Windows subroutine CORRECT (theorems 3-4): shared bl_tmc infra.  *)
(*                                                                            *)
(* The Windows .obj is the INLINE-SHIM model.  Its trimmed machine code is    *)
(*   windows_tmc pc kk = shim(42) ++ COMMON(820) ++ tail(34)   (= 896)        *)
(* where shim(42) = push rdi; push rsi; mov rcx->rdi; mov rdx->rsi;           *)
(* mov r8->rdx; sub rsp,0x50; movups xmm6..10 -> [rsp+0/16/32/48/64] (the     *)
(* d5989555 Windows callee-saved-XMM fix), tail(34) = movups xmm6..10 restore *)
(* + add rsp,0x50 + pop rsi; pop rdi; ret, and COMMON is byte-identical to    *)
(* BUTLAST(sysv_tmc) modulo the riprel LEA-K256 displacement, which shifts by  *)
(* the 42-byte shim: the sysv tmc lea atom is `&kk - (&pc + -- &117)`, the     *)
(* windows tmc lea atom is `&kk - (&pc + -- &75)`, and (pc+42)-117 = pc-75, so *)
(* BUTLAST(sysv_tmc @ pc+42)'s lea folds to the windows lea.  The SysV tmc =   *)
(* COMMON ++ [ret]; the Windows image lacks the SysV trailing `ret` (it has a  *)
(* movups there), so ONLY BUTLAST(sysv_tmc) is a subprogram of windows_tmc.    *)
(* Hence the committed SysV full-tmc CORE_CORRECT CANNOT be reused: weakening  *)
(* a full-tmc PRE to a BUTLAST PRE is the UNSOUND direction (bytes_loaded of a *)
(* BUTLAST does not determine the dropped byte).  The entire CORE_CORRECT cone *)
(* is re-stated over `sha256_compress_hw_bl_tmc` (= BUTLAST sysv_tmc), which   *)
(* DECODES IDENTICALLY for all rows in [0,820); the re-statement is mechanical *)
(* (bl_of_stmt: sysv_tmc -> bl_tmc, 825/821 -> 820) with the committed tactic  *)
(* replayed against SHA256_COMPRESS_HW_BL_EXEC.  Template: the completed nohw  *)
(* Phase-12 chain (x86/proofs/sha256_compress.ml L9253-9313).                  *)
(* ========================================================================== *)

(* ---- The 42-byte ABI shim prefix and the 34-byte non-pop epilogue tail. ---- *)
let HW_WIN_SHIM42 = `[word 0x57; word 0x56; word 0x48; word 0x89; word 0xcf;
   word 0x48; word 0x89; word 0xd6; word 0x4c; word 0x89; word 0xc2;
   word 0x48; word 0x83; word 0xec; word 0x50;
   word 0x0f; word 0x11; word 0x34; word 0x24;
   word 0x0f; word 0x11; word 0x7c; word 0x24; word 0x10;
   word 0x44; word 0x0f; word 0x11; word 0x44; word 0x24; word 0x20;
   word 0x44; word 0x0f; word 0x11; word 0x4c; word 0x24; word 0x30;
   word 0x44; word 0x0f; word 0x11; word 0x54; word 0x24; word 0x40]:byte list`;;
let HW_WIN_TAIL34 = `[word 0x0f; word 0x10; word 0x34; word 0x24;
   word 0x0f; word 0x10; word 0x7c; word 0x24; word 0x10;
   word 0x44; word 0x0f; word 0x10; word 0x44; word 0x24; word 0x20;
   word 0x44; word 0x0f; word 0x10; word 0x4c; word 0x24; word 0x30;
   word 0x44; word 0x0f; word 0x10; word 0x54; word 0x24; word 0x40;
   word 0x48; word 0x83; word 0xc4; word 0x50;
   word 0x5e; word 0x5f; word 0xc3]:byte list`;;

(* ---- WIN_DECOMP: windows_tmc = shim42 ++ BUTLAST(sysv_tmc @ pc+42) ++ tail34 ---- *)
let SHA256_HW_WIN_RIPREL_ALIGN =
  INT_ARITH `(&pc + &42) + -- &117:int = &pc + -- &75`;;

let SHA256_HW_WIN_DECOMP =
  let appf = `APPEND:byte list->byte list->byte list` in
  let butl = `BUTLAST (sha256_compress_hw_tmc (pc+42) kk)` in
  let rhs_tm = mk_comb(mk_comb(appf, HW_WIN_SHIM42),
                mk_comb(mk_comb(appf, butl), HW_WIN_TAIL34)) in
  prove
   (mk_eq(`sha256_compress_hw_windows_tmc pc kk`, rhs_tm),
    REWRITE_TAC[sha256_compress_hw_windows_tmc; sha256_compress_hw_windows_mc;
                sha256_compress_hw_tmc; sha256_compress_hw_mc] THEN
    REWRITE_TAC[BUTLAST_CLAUSES; APPEND] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
    REWRITE_TAC[SHA256_HW_WIN_RIPREL_ALIGN] THEN REWRITE_TAC[]);;

(* ---- WIN_BODY_BRIDGE: the windows->sysv-body bytes_loaded bridge. -------- *)
let SHA256_HW_WIN_BODY_BRIDGE = prove
 (`bytes_loaded s (word pc) (sha256_compress_hw_windows_tmc pc kk)
   ==> bytes_loaded s (word (pc + 42))
          (BUTLAST (sha256_compress_hw_tmc (pc + 42) kk))`,
  REWRITE_TAC[SHA256_HW_WIN_DECOMP; bytes_loaded_append; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  REWRITE_TAC[ARITH_RULE `pc + 42 = 42 + pc`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* ---- bl_tmc: the BUTLAST core program + its EXEC (decode rows [0,820)). ---- *)
(* X86_MK_EXEC on BUTLAST of the reloc tmc fails via AP_TERM (X86_TRIM_EXEC),   *)
(* so name the reduced BUTLAST list as its own constant and MK_EXEC that.       *)
let sha256_compress_hw_bl_tmc = new_definition
 `sha256_compress_hw_bl_tmc pc kk =
    BUTLAST (sha256_compress_hw_tmc pc kk)`;;

let SHA256_HW_BL_TMC_RED =
  REWRITE_RULE[sha256_compress_hw_tmc; BUTLAST_CLAUSES]
    (SPEC_ALL sha256_compress_hw_bl_tmc);;

let SHA256_COMPRESS_HW_BL_EXEC = X86_MK_EXEC_RULE SHA256_HW_BL_TMC_RED;;

Printf.printf "S060_WIN_BL_INFRA: DECOMP hyps=%d BODY_BRIDGE hyps=%d BL_EXEC_LEN=%s\n%!"
  (List.length(hyp SHA256_HW_WIN_DECOMP))
  (List.length(hyp SHA256_HW_WIN_BODY_BRIDGE))
  (string_of_term(rhs(concl(fst SHA256_COMPRESS_HW_BL_EXEC))));;

(* -------------------------------------------------------------------------- *)
(* bl_tmc cone-port infrastructure + beachhead (session 060).                 *)
(*                                                                            *)
(* The Windows wrapper MPs a CORE_CORRECT proved over `sha256_compress_hw_    *)
(* bl_tmc` (= BUTLAST sysv_tmc).  Because bl_tmc DECODES IDENTICALLY to        *)
(* sysv_tmc for every row in [0,820), each committed cone lemma is re-stated   *)
(* over bl_tmc purely mechanically — `bl_of_stmt` swaps the code constant      *)
(* (and, for lemmas carrying the mc-length region numeral 825, maps it to the  *)
(* bl length 820) — and RE-PROVED by REPLAYING the committed tactic VERBATIM   *)
(* with SHA256_COMPRESS_HW_EXEC -> SHA256_COMPRESS_HW_BL_EXEC.  The LCF kernel  *)
(* is the soundness oracle: a wrong substitution or a row that decoded         *)
(* differently would fail the replayed stepping.  Template: nohw Phase-12      *)
(* (`bl_of_stmt`, x86/proofs/sha256_compress.ml L9334).                        *)
(* -------------------------------------------------------------------------- *)

(* code-constant swap; the region-length variant (825->820) is applied only    *)
(* to the higher lemmas that carry the caller nonoverlap region (CORE_ABS,      *)
(* CORE_ABS_SPEC, core_correct_tm, wrappers).                                   *)
let bl_of_stmt tm =
  subst [`sha256_compress_hw_bl_tmc`,`sha256_compress_hw_tmc`] tm;;
let bl_of_stmt_reg tm =
  subst [`820`,`825`] (bl_of_stmt tm);;

(* bytes_loaded_update rule keyed on the bl EXEC, for the composed _BL legs.    *)
let execup_bl = MATCH_MP bytes_loaded_update (fst SHA256_COMPRESS_HW_BL_EXEC);;

(* Beachhead: the K-load atom over bl_tmc (validates the leaf-port mechanism    *)
(* end-to-end in-file: verbose-step + SIMD refold closer replays verbatim over  *)
(* BL_EXEC; bl_tmc decodes rows [0,820) identically).                          *)
let SHA256_COMPRESS_HW_KLOAD4_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_KLOAD4),
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s2" THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[]);;

Printf.printf "S060_BLPORT_BEACHHEAD: KLOAD4_BL hyps=%d frees=%d (mechanism validated in-file)\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_KLOAD4_BL))
  (List.length(frees(concl SHA256_COMPRESS_HW_KLOAD4_BL)));;

(* ========================================================================== *)
(* Session 061 — bl_tmc cone-port: the 48 STEPPED-LEAF _BL lemmas.            *)
(*                                                                            *)
(* Each is `bl_of_stmt[_reg] (concl COMMITTED)` proved by REPLAYING the        *)
(* committed tactic VERBATIM with SHA256_COMPRESS_HW_EXEC ->                   *)
(* SHA256_COMPRESS_HW_BL_EXEC and every cone-lemma reference X -> X_BL.        *)
(* bl_tmc = BUTLAST(sysv_tmc) decodes rows [0,820) IDENTICALLY, so the         *)
(* stepping + SIMD-refold closers close unchanged; the LCF kernel re-checks    *)
(* every replayed step (a wrong swap would fail stepping, not pass silently).  *)
(* This is the validated KLOAD4_BL beachhead (s060) applied uniformly to the   *)
(* stepped leaves; the 5 gen_group_038 groups (G8-G12) + the composer tower    *)
(* (CORE_TAIL3/HEAD/HEAD38_RAW/CORE_*_TO_2F0/CORE_LOOP_BODY*/                   *)
(* CORE_LOOP_STEP_RAW/CORE_CORRECT) follow in later blocks.  Generated by      *)
(* orchestrator/logs/s061_gen_bl.py; validated hyps=0 frees=0 on s055cold.     *)
(* ========================================================================== *)
let SHA256_COMPRESS_HW_GROUP4_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP4),

  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s5" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SHA256_RNDS2_WK_CONG THEN CONJ_TAC THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP4_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP4_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP4_BL)));;

let SHA256_COMPRESS_HW_GROUP4_PACKED_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP4_PACKED),

  let GA = CONV_RULE(TOP_DEPTH_CONV let_CONV)
             (SPECL [`l:int32 list`; `wk:int128`] SHA256_RNDS2_GROUP_ADVANCE) in
  let GA1 = CONJUNCT1 GA and GA2 = CONJUNCT2 GA in
  let ATCF = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`l:int32 list`;
             `word_subword wk (0,32):int32`; `word_subword wk (32,32):int32`;
             `word_subword wk (64,32):int32`; `word_subword wk (96,32):int32`]
            ABEF_TWO_IS_CDGH_FOUR) in
  REPEAT GEN_TAC THEN REWRITE_TAC[CR4] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA2] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM ATCF] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA1] THEN
  MATCH_ACCEPT_TAC SHA256_COMPRESS_HW_GROUP4_BL);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP4_PACKED_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP4_PACKED_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP4_PACKED_BL)));;

let SHA256_COMPRESS_HW_GROUP_STEP4_SM_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP_STEP4_SM),

  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s5" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s6" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s7" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s8" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s9" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC SHA256_RNDS2_WK_CONG THEN CONJ_TAC THEN
      CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC) THEN
  TRY REFL_TAC);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP_STEP4_SM_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP_STEP4_SM_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP_STEP4_SM_BL)));;

let SHA256_COMPRESS_HW_GROUP_STEP4_SM_PACKED_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP_STEP4_SM_PACKED),

  let GA = CONV_RULE(TOP_DEPTH_CONV let_CONV)
             (SPECL [`l:int32 list`; `wk:int128`] SHA256_RNDS2_GROUP_ADVANCE) in
  let GA1 = CONJUNCT1 GA and GA2 = CONJUNCT2 GA in
  let ATCF = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`l:int32 list`;
             `word_subword wk (0,32):int32`; `word_subword wk (32,32):int32`;
             `word_subword wk (64,32):int32`; `word_subword wk (96,32):int32`]
            ABEF_TWO_IS_CDGH_FOUR) in
  REPEAT GEN_TAC THEN REWRITE_TAC[CR4] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA2] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM ATCF] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA1] THEN
  MATCH_ACCEPT_TAC SHA256_COMPRESS_HW_GROUP_STEP4_SM_BL);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP_STEP4_SM_PACKED_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP_STEP4_SM_PACKED_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP_STEP4_SM_PACKED_BL)));;

let SHA256_COMPRESS_HW_GROUP4_FULL_S_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP4_FULL_S),

  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0xfc`
   `\s. read RCX s = kptr /\
        read (memory :> bytes128 (word_add kptr (word 32))) s = kq1 /\
        word_subword (read YMM0_SSE s) (0,128) = simd4 word_add kq a3 /\
        word_subword (read YMM1_SSE s) (0,128) =
          ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
        word_subword (read YMM2_SSE s) (0,128) =
          CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
        word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
        word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
        word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
        word_subword (read YMM6_SSE s) (0,128) = (a6:int128)` THEN
  CONJ_TAC THENL
   [(* leg 1: K-load pc+0xf4 .. pc+0xfc; RCX/Kmem@kptr+32/YMM1..6 ride through *)
    ENSURES_INIT_TAC "s0" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s2" THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
    REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[];
    (* leg 2: the memory-threaded packed group-step, wk := simd4 word_add kq a3.  *)
    (* Bare MATCH_ACCEPT lets the higher-order matcher instantiate the binders    *)
    (* from the leg goal (mloc := kptr+32, wk := simd4 word_add kq a3, etc.),      *)
    (* avoiding a hand-typed SPECL of the polymorphic simd4 term.                 *)
    MATCH_ACCEPT_TAC(REWRITE_RULE[SOME_FLAGS]
        SHA256_COMPRESS_HW_GROUP_STEP4_SM_PACKED_BL)]);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP4_FULL_S_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP4_FULL_S_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP4_FULL_S_BL)));;

let SHA256_COMPRESS_HW_GROUP_STEP4_SM_R1_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP_STEP4_SM_R1),

  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s5" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s6" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s7" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s8" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s9" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC SHA256_RNDS2_WK_CONG THEN CONJ_TAC THEN
      CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC) THEN
  TRY REFL_TAC);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP_STEP4_SM_R1_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP_STEP4_SM_R1_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP_STEP4_SM_R1_BL)));;

let SHA256_COMPRESS_HW_GROUP_STEP4_SM_R1_PACKED_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP_STEP4_SM_R1_PACKED),

  let GA = CONV_RULE(TOP_DEPTH_CONV let_CONV)
             (SPECL [`l:int32 list`; `wk:int128`] SHA256_RNDS2_GROUP_ADVANCE) in
  let GA1 = CONJUNCT1 GA and GA2 = CONJUNCT2 GA in
  let ATCF = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`l:int32 list`;
             `word_subword wk (0,32):int32`; `word_subword wk (32,32):int32`;
             `word_subword wk (64,32):int32`; `word_subword wk (96,32):int32`]
            ABEF_TWO_IS_CDGH_FOUR) in
  REPEAT GEN_TAC THEN REWRITE_TAC[CR4] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA2] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM ATCF] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA1] THEN
  MATCH_ACCEPT_TAC SHA256_COMPRESS_HW_GROUP_STEP4_SM_R1_BL);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP_STEP4_SM_R1_PACKED_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP_STEP4_SM_R1_PACKED_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP_STEP4_SM_R1_PACKED_BL)));;

let SHA256_COMPRESS_HW_GROUP4_FULL_S_R1_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP4_FULL_S_R1),

  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x129`
   `\s. read RCX s = kptr /\
        read (memory :> bytes128 (word_add kptr (word 64))) s = kq2 /\
        word_subword (read YMM0_SSE s) (0,128) = simd4 word_add kq1 a4 /\
        word_subword (read YMM1_SSE s) (0,128) =
          ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
        word_subword (read YMM2_SSE s) (0,128) =
          CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
        word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
        word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
        word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
        word_subword (read YMM6_SSE s) (0,128) = (a6:int128)` THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s2" THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
    REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC(REWRITE_RULE[SOME_FLAGS]
        SHA256_COMPRESS_HW_GROUP_STEP4_SM_R1_PACKED_BL)]);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP4_FULL_S_R1_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP4_FULL_S_R1_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP4_FULL_S_R1_BL)));;

let SHA256_COMPRESS_HW_GROUP_STEP4_SM_R2_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP_STEP4_SM_R2),

  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s5" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s6" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s7" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s8" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s9" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC SHA256_RNDS2_WK_CONG THEN CONJ_TAC THEN
      CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC) THEN
  TRY REFL_TAC);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP_STEP4_SM_R2_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP_STEP4_SM_R2_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP_STEP4_SM_R2_BL)));;

let SHA256_COMPRESS_HW_GROUP_STEP4_SM_R2_PACKED_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP_STEP4_SM_R2_PACKED),

  let GA = CONV_RULE(TOP_DEPTH_CONV let_CONV)
             (SPECL [`l:int32 list`; `wk:int128`] SHA256_RNDS2_GROUP_ADVANCE) in
  let GA1 = CONJUNCT1 GA and GA2 = CONJUNCT2 GA in
  let ATCF = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`l:int32 list`;
             `word_subword wk (0,32):int32`; `word_subword wk (32,32):int32`;
             `word_subword wk (64,32):int32`; `word_subword wk (96,32):int32`]
            ABEF_TWO_IS_CDGH_FOUR) in
  REPEAT GEN_TAC THEN REWRITE_TAC[CR4] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA2] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM ATCF] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA1] THEN
  MATCH_ACCEPT_TAC SHA256_COMPRESS_HW_GROUP_STEP4_SM_R2_BL);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP_STEP4_SM_R2_PACKED_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP_STEP4_SM_R2_PACKED_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP_STEP4_SM_R2_PACKED_BL)));;

let SHA256_COMPRESS_HW_GROUP4_FULL_S_R2_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP4_FULL_S_R2),

  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x156`
   `\s. read RCX s = kptr /\
        read (memory :> bytes128 (word_add kptr (word 96))) s = kq3 /\
        word_subword (read YMM0_SSE s) (0,128) = simd4 word_add kq2 a5 /\
        word_subword (read YMM1_SSE s) (0,128) =
          ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
        word_subword (read YMM2_SSE s) (0,128) =
          CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
        word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
        word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
        word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
        word_subword (read YMM6_SSE s) (0,128) = (a6:int128)` THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s2" THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
    REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC(REWRITE_RULE[SOME_FLAGS]
        SHA256_COMPRESS_HW_GROUP_STEP4_SM_R2_PACKED_BL)]);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP4_FULL_S_R2_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP4_FULL_S_R2_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP4_FULL_S_R2_BL)));;

let SHA256_COMPRESS_HW_GROUP_STEP4_SM_R3_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP_STEP4_SM_R3),

  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s5" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s6" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s7" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s8" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s9" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC SHA256_RNDS2_WK_CONG THEN CONJ_TAC THEN
      CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC) THEN
  TRY REFL_TAC);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP_STEP4_SM_R3_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP_STEP4_SM_R3_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP_STEP4_SM_R3_BL)));;

let SHA256_COMPRESS_HW_GROUP_STEP4_SM_R3_PACKED_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP_STEP4_SM_R3_PACKED),

  let GA = CONV_RULE(TOP_DEPTH_CONV let_CONV)
             (SPECL [`l:int32 list`; `wk:int128`] SHA256_RNDS2_GROUP_ADVANCE) in
  let GA1 = CONJUNCT1 GA and GA2 = CONJUNCT2 GA in
  let ATCF = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`l:int32 list`;
             `word_subword wk (0,32):int32`; `word_subword wk (32,32):int32`;
             `word_subword wk (64,32):int32`; `word_subword wk (96,32):int32`]
            ABEF_TWO_IS_CDGH_FOUR) in
  REPEAT GEN_TAC THEN REWRITE_TAC[CR4] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA2] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM ATCF] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA1] THEN
  MATCH_ACCEPT_TAC SHA256_COMPRESS_HW_GROUP_STEP4_SM_R3_BL);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP_STEP4_SM_R3_PACKED_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP_STEP4_SM_R3_PACKED_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP_STEP4_SM_R3_PACKED_BL)));;

let SHA256_COMPRESS_HW_GROUP4_FULL_S_R3_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP4_FULL_S_R3),

  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x183`
   `\s. read RCX s = kptr /\
        read (memory :> bytes128 (word_add kptr (word 128))) s = kq4 /\
        word_subword (read YMM0_SSE s) (0,128) = simd4 word_add kq3 a6 /\
        word_subword (read YMM1_SSE s) (0,128) =
          ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
        word_subword (read YMM2_SSE s) (0,128) =
          CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
        word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
        word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
        word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
        word_subword (read YMM6_SSE s) (0,128) = (a6:int128)` THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s2" THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
    REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC(REWRITE_RULE[SOME_FLAGS]
        SHA256_COMPRESS_HW_GROUP_STEP4_SM_R3_PACKED_BL)]);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP4_FULL_S_R3_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP4_FULL_S_R3_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP4_FULL_S_R3_BL)));;

let SHA256_COMPRESS_HW_SPEC_STEP_R0_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_SPEC_STEP_R0),

  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`m:int32 list`; `g:num`] R0_YMM4) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`m:int32 list`; `g:num`] R0_YMM5) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`m:int32 list`; `g:num`] R0_YMM6) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(INST
    [ `WWIN m (4*g) : int128`, `a3:int128`;
      `PADP m (4*g - 12) : int128`, `a4:int128`;
      `MSG1P m (4*g - 8) : int128`, `a5:int128`;
      `WWIN m (4*g - 4) : int128`, `a6:int128`;
      `WQUAD (EL (4*g) sha256_constants) (EL (4*g+1) sha256_constants)
             (EL (4*g+2) sha256_constants) (EL (4*g+3) sha256_constants) : int128`,
        `kq:int128`;
      `sha256_compress_rounds m (st:int32 list) (4*g) : int32 list`, `l:int32 list` ]
    (SPEC_ALL SHA256_COMPRESS_HW_GROUP4_FULL_S_BL)) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[CR4_SPEC_STEP_WWIN] THEN
  DISCH_THEN ACCEPT_TAC);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_SPEC_STEP_R0_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_SPEC_STEP_R0_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_SPEC_STEP_R0_BL)));;

let SHA256_COMPRESS_HW_SPEC_STEP_R1_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_SPEC_STEP_R1),

  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`m:int32 list`; `g:num`] R0_YMM4) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`m:int32 list`; `g:num`] R0_YMM5) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`m:int32 list`; `g:num`] R0_YMM6) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(INST
    [ `WWIN m (4*g - 4) : int128`, `a3:int128`;
      `WWIN m (4*g) : int128`, `a4:int128`;
      `PADP m (4*g - 12) : int128`, `a5:int128`;
      `MSG1P m (4*g - 8) : int128`, `a6:int128`;
      `WQUAD (EL (4*g) sha256_constants) (EL (4*g+1) sha256_constants)
             (EL (4*g+2) sha256_constants) (EL (4*g+3) sha256_constants) : int128`,
        `kq1:int128`;
      `sha256_compress_rounds m (st:int32 list) (4*g) : int32 list`, `l:int32 list` ]
    (SPEC_ALL SHA256_COMPRESS_HW_GROUP4_FULL_S_R1_BL)) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[CR4_SPEC_STEP_WWIN] THEN
  DISCH_THEN ACCEPT_TAC);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_SPEC_STEP_R1_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_SPEC_STEP_R1_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_SPEC_STEP_R1_BL)));;

let SHA256_COMPRESS_HW_SPEC_STEP_R2_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_SPEC_STEP_R2),

  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`m:int32 list`; `g:num`] R0_YMM4) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`m:int32 list`; `g:num`] R0_YMM5) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`m:int32 list`; `g:num`] R0_YMM6) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(INST
    [ `MSG1P m (4*g - 8) : int128`, `a3:int128`;
      `WWIN m (4*g - 4) : int128`, `a4:int128`;
      `WWIN m (4*g) : int128`, `a5:int128`;
      `PADP m (4*g - 12) : int128`, `a6:int128`;
      `WQUAD (EL (4*g) sha256_constants) (EL (4*g+1) sha256_constants)
             (EL (4*g+2) sha256_constants) (EL (4*g+3) sha256_constants) : int128`, `kq2:int128`;
      `sha256_compress_rounds m (st:int32 list) (4*g) : int32 list`, `l:int32 list` ]
    (SPEC_ALL SHA256_COMPRESS_HW_GROUP4_FULL_S_R2_BL)) THEN
  ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[CR4_SPEC_STEP_WWIN] THEN DISCH_THEN ACCEPT_TAC);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_SPEC_STEP_R2_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_SPEC_STEP_R2_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_SPEC_STEP_R2_BL)));;

let SHA256_COMPRESS_HW_SPEC_STEP_R3_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_SPEC_STEP_R3),

  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`m:int32 list`; `g:num`] R0_YMM4) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`m:int32 list`; `g:num`] R0_YMM5) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`m:int32 list`; `g:num`] R0_YMM6) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(INST
    [ `PADP m (4*g - 12) : int128`, `a3:int128`;
      `MSG1P m (4*g - 8) : int128`, `a4:int128`;
      `WWIN m (4*g - 4) : int128`, `a5:int128`;
      `WWIN m (4*g) : int128`, `a6:int128`;
      `WQUAD (EL (4*g) sha256_constants) (EL (4*g+1) sha256_constants)
             (EL (4*g+2) sha256_constants) (EL (4*g+3) sha256_constants) : int128`, `kq3:int128`;
      `sha256_compress_rounds m (st:int32 list) (4*g) : int32 list`, `l:int32 list` ]
    (SPEC_ALL SHA256_COMPRESS_HW_GROUP4_FULL_S_R3_BL)) THEN
  ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[CR4_SPEC_STEP_WWIN] THEN DISCH_THEN ACCEPT_TAC);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_SPEC_STEP_R3_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_SPEC_STEP_R3_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_SPEC_STEP_R3_BL)));;

let SHA256_COMPRESS_HW_GROUP_STEP4_G13_RAW_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP_STEP4_G13_RAW),

  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s5" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s6" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s7" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC SHA256_RNDS2_WK_CONG THEN CONJ_TAC THEN
      CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC) THEN
  TRY REFL_TAC);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP_STEP4_G13_RAW_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP_STEP4_G13_RAW_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP_STEP4_G13_RAW_BL)));;

let SHA256_COMPRESS_HW_GROUP_STEP4_G13_PACKED_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP_STEP4_G13_PACKED),

  let GA = CONV_RULE(TOP_DEPTH_CONV let_CONV)
             (SPECL [`l:int32 list`; `wk:int128`] SHA256_RNDS2_GROUP_ADVANCE) in
  let GA1 = CONJUNCT1 GA and GA2 = CONJUNCT2 GA in
  let ATCF = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`l:int32 list`;
             `word_subword wk (0,32):int32`; `word_subword wk (32,32):int32`;
             `word_subword wk (64,32):int32`; `word_subword wk (96,32):int32`]
            ABEF_TWO_IS_CDGH_FOUR) in
  REPEAT GEN_TAC THEN REWRITE_TAC[CR4] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA2] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM ATCF] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA1] THEN
  MATCH_ACCEPT_TAC SHA256_COMPRESS_HW_GROUP_STEP4_G13_RAW_BL);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP_STEP4_G13_PACKED_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP_STEP4_G13_PACKED_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP_STEP4_G13_PACKED_BL)));;

let SHA256_COMPRESS_HW_GROUP4_FULL_S_G13_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP4_FULL_S_G13),

  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x2a3`
   `\s. read RCX s = kptr /\
        read (memory :> bytes128 (word_add kptr (word 320))) s = kq1 /\
        word_subword (read YMM0_SSE s) (0,128) = simd4 word_add kq a4 /\
        word_subword (read YMM1_SSE s) (0,128) =
          ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
        word_subword (read YMM2_SSE s) (0,128) =
          CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
        word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
        word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
        word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
        word_subword (read YMM6_SSE s) (0,128) = (a6:int128)` THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s2" THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
    REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC(REWRITE_RULE[SOME_FLAGS]
        SHA256_COMPRESS_HW_GROUP_STEP4_G13_PACKED_BL)]);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP4_FULL_S_G13_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP4_FULL_S_G13_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP4_FULL_S_G13_BL)));;

let SHA256_COMPRESS_HW_GROUP_STEP4_G14_RAW_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP_STEP4_G14_RAW),

  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s5" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC SHA256_RNDS2_WK_CONG THEN CONJ_TAC THEN
      CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC) THEN
  TRY REFL_TAC);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP_STEP4_G14_RAW_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP_STEP4_G14_RAW_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP_STEP4_G14_RAW_BL)));;

let SHA256_COMPRESS_HW_GROUP_STEP4_G14_PACKED_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP_STEP4_G14_PACKED),

  let GA = CONV_RULE(TOP_DEPTH_CONV let_CONV)
             (SPECL [`l:int32 list`; `wk:int128`] SHA256_RNDS2_GROUP_ADVANCE) in
  let GA1 = CONJUNCT1 GA and GA2 = CONJUNCT2 GA in
  let ATCF = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`l:int32 list`;
             `word_subword wk (0,32):int32`; `word_subword wk (32,32):int32`;
             `word_subword wk (64,32):int32`; `word_subword wk (96,32):int32`]
            ABEF_TWO_IS_CDGH_FOUR) in
  REPEAT GEN_TAC THEN REWRITE_TAC[CR4] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA2] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM ATCF] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA1] THEN
  MATCH_ACCEPT_TAC SHA256_COMPRESS_HW_GROUP_STEP4_G14_RAW_BL);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP_STEP4_G14_PACKED_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP_STEP4_G14_PACKED_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP_STEP4_G14_PACKED_BL)));;

let SHA256_COMPRESS_HW_GROUP4_FULL_S_G14_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP4_FULL_S_G14),

  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x2ce`
   `\s. read RCX s = kptr /\
        read (memory :> bytes128 (word_add kptr (word 352))) s = kq1 /\
        word_subword (read YMM0_SSE s) (0,128) = simd4 word_add kq a5 /\
        word_subword (read YMM1_SSE s) (0,128) =
          ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
        word_subword (read YMM2_SSE s) (0,128) =
          CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
        word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
        word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
        word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
        word_subword (read YMM6_SSE s) (0,128) = (a6:int128)` THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s2" THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
    REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC(REWRITE_RULE[SOME_FLAGS]
        SHA256_COMPRESS_HW_GROUP_STEP4_G14_PACKED_BL)]);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP4_FULL_S_G14_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP4_FULL_S_G14_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP4_FULL_S_G14_BL)));;

let SHA256_COMPRESS_HW_GROUP_STEP4_G15_RAW_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP_STEP4_G15_RAW),

  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s5" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s6" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC SHA256_RNDS2_WK_CONG THEN CONJ_TAC THEN
      CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC) THEN
  TRY REFL_TAC);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP_STEP4_G15_RAW_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP_STEP4_G15_RAW_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP_STEP4_G15_RAW_BL)));;

let SHA256_COMPRESS_HW_GROUP_STEP4_G15_PACKED_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP_STEP4_G15_PACKED),

  let GA = CONV_RULE(TOP_DEPTH_CONV let_CONV)
             (SPECL [`l:int32 list`; `wk:int128`] SHA256_RNDS2_GROUP_ADVANCE) in
  let GA1 = CONJUNCT1 GA and GA2 = CONJUNCT2 GA in
  let ATCF = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`l:int32 list`;
             `word_subword wk (0,32):int32`; `word_subword wk (32,32):int32`;
             `word_subword wk (64,32):int32`; `word_subword wk (96,32):int32`]
            ABEF_TWO_IS_CDGH_FOUR) in
  REPEAT GEN_TAC THEN REWRITE_TAC[CR4] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA2] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM ATCF] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA1] THEN
  MATCH_ACCEPT_TAC SHA256_COMPRESS_HW_GROUP_STEP4_G15_RAW_BL);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP_STEP4_G15_PACKED_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP_STEP4_G15_PACKED_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP_STEP4_G15_PACKED_BL)));;

let SHA256_COMPRESS_HW_GROUP4_FULL_S_G15_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP4_FULL_S_G15),

  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x2f0`
   `\s. read RCX s = kptr /\
        read (memory :> bytes128 (word_add kptr (word 352))) s = kq /\
        word_subword (read YMM0_SSE s) (0,128) = simd4 word_add kq a6 /\
        word_subword (read YMM1_SSE s) (0,128) =
          ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
        word_subword (read YMM2_SSE s) (0,128) =
          CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
        word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
        word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
        word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
        word_subword (read YMM6_SSE s) (0,128) = (a6:int128)` THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s2" THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
    REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC(REWRITE_RULE[SOME_FLAGS]
        SHA256_COMPRESS_HW_GROUP_STEP4_G15_PACKED_BL)]);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP4_FULL_S_G15_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP4_FULL_S_G15_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP4_FULL_S_G15_BL)));;

let SHA256_COMPRESS_HW_FEEDFWD_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_FEEDFWD),

  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s2" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  TRY REFL_TAC);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_FEEDFWD_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_FEEDFWD_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_FEEDFWD_BL)));;

let SHA256_COMPRESS_HW_ENTRY_REPACK_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_ENTRY_REPACK),

  REPEAT GEN_TAC THEN DISCH_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s5" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s6" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s7" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s8" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s9" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s10" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ABEF_PACK; CDGH_PACK] THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REPEAT CONJ_TAC THEN TRY REFL_TAC THEN CONV_TAC WORD_BLAST);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_ENTRY_REPACK_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_ENTRY_REPACK_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_ENTRY_REPACK_BL)));;

let SHA256_COMPRESS_HW_HEAD_MSGLOAD0_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_HEAD_MSGLOAD0),

  let LANE = WORD_BLAST
    `word_bytereverse (w:int32) =
       (word_join:byte->24 word->int32) (word_subword w (0,8))
        ((word_join:byte->16 word->24 word) (word_subword w (8,8))
         ((word_join:byte->8 word->16 word) (word_subword w (16,8))
          (word_subword w (24,8))))` in
  REPEAT GEN_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s5" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[usimd4; usimd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  GEN_REWRITE_TAC (DEPTH_CONV) [LANE] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_BLAST);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_HEAD_MSGLOAD0_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_HEAD_MSGLOAD0_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_HEAD_MSGLOAD0_BL)));;

let SHA256_COMPRESS_HW_GROUP_STEP4_G0_RAW_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP_STEP4_G0_RAW),

  let LANE = WORD_BLAST
    `word_bytereverse (w:int32) =
       (word_join:byte->24 word->int32) (word_subword w (0,8))
        ((word_join:byte->16 word->24 word) (word_subword w (8,8))
         ((word_join:byte->8 word->16 word) (word_subword w (16,8))
          (word_subword w (24,8))))` in
  REPEAT GEN_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s5" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s6" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s7" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC SHA256_RNDS2_WK_CONG THEN CONJ_TAC THEN
      CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC) THEN
  TRY REFL_TAC THEN
  REWRITE_TAC[usimd4; usimd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  GEN_REWRITE_TAC (DEPTH_CONV) [LANE] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_BLAST);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP_STEP4_G0_RAW_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP_STEP4_G0_RAW_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP_STEP4_G0_RAW_BL)));;

let SHA256_COMPRESS_HW_GROUP_STEP4_G0_PACKED_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP_STEP4_G0_PACKED),

  let GA = CONV_RULE(TOP_DEPTH_CONV let_CONV)
             (SPECL [`l:int32 list`; `wk:int128`] SHA256_RNDS2_GROUP_ADVANCE) in
  let GA1 = CONJUNCT1 GA and GA2 = CONJUNCT2 GA in
  let ATCF = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`l:int32 list`;
             `word_subword wk (0,32):int32`; `word_subword wk (32,32):int32`;
             `word_subword wk (64,32):int32`; `word_subword wk (96,32):int32`]
            ABEF_TWO_IS_CDGH_FOUR) in
  REPEAT GEN_TAC THEN REWRITE_TAC[CR4] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA2] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM ATCF] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA1] THEN
  MATCH_ACCEPT_TAC SHA256_COMPRESS_HW_GROUP_STEP4_G0_RAW_BL);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP_STEP4_G0_PACKED_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP_STEP4_G0_PACKED_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP_STEP4_G0_PACKED_BL)));;

let SHA256_COMPRESS_HW_GROUP4_FULL_S_G0_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP4_FULL_S_G0),

  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + 0x59`
   `\s. read RCX s = kptr /\
        read (memory :> bytes128 (word_add kptr (word 18446744073709551520))) s = kq1 /\
        word_subword (read YMM0_SSE s) (0,128) = simd4 word_add kq0 a3 /\
        word_subword (read YMM1_SSE s) (0,128) =
          ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
        word_subword (read YMM2_SSE s) (0,128) =
          CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
        word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
        word_subword (read YMM4_SSE s) (0,128) = (m1r:int128) /\
        word_subword (read YMM7_SSE s) (0,128) =
          (word 16018520953223639909183530438118932995 : int128)` THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s2" THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
    REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC SHA256_COMPRESS_HW_GROUP_STEP4_G0_PACKED_BL]);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP4_FULL_S_G0_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP4_FULL_S_G0_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP4_FULL_S_G0_BL)));;

let SHA256_COMPRESS_HW_GROUP_STEP4_G1_RAW_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP_STEP4_G1_RAW),

  let LANE = WORD_BLAST
    `word_bytereverse (w:int32) =
       (word_join:byte->24 word->int32) (word_subword w (0,8))
        ((word_join:byte->16 word->24 word) (word_subword w (8,8))
         ((word_join:byte->8 word->16 word) (word_subword w (16,8))
          (word_subword w (24,8))))` in
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s5" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s6" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC SHA256_RNDS2_WK_CONG THEN CONJ_TAC THEN
      CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC) THEN
  TRY REFL_TAC THEN
  REWRITE_TAC[usimd4; usimd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  GEN_REWRITE_TAC (DEPTH_CONV) [LANE] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_BLAST);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP_STEP4_G1_RAW_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP_STEP4_G1_RAW_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP_STEP4_G1_RAW_BL)));;

let SHA256_COMPRESS_HW_GROUP_STEP4_G1_PACKED_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP_STEP4_G1_PACKED),

  let GA = CONV_RULE(TOP_DEPTH_CONV let_CONV)
             (SPECL [`l:int32 list`; `wk:int128`] SHA256_RNDS2_GROUP_ADVANCE) in
  let GA1 = CONJUNCT1 GA and GA2 = CONJUNCT2 GA in
  let ATCF = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`l:int32 list`;
             `word_subword wk (0,32):int32`; `word_subword wk (32,32):int32`;
             `word_subword wk (64,32):int32`; `word_subword wk (96,32):int32`]
            ABEF_TWO_IS_CDGH_FOUR) in
  REPEAT GEN_TAC THEN REWRITE_TAC[CR4] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA2] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM ATCF] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA1] THEN
  MATCH_ACCEPT_TAC SHA256_COMPRESS_HW_GROUP_STEP4_G1_RAW_BL);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP_STEP4_G1_PACKED_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP_STEP4_G1_PACKED_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP_STEP4_G1_PACKED_BL)));;

let SHA256_COMPRESS_HW_GROUP4_FULL_S_G1_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP4_FULL_S_G1),

  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x7f`
   `\s. read RCX s = kptr /\
        read RSI s = dptr /\
        read (memory :> bytes128 (word_add kptr (word 18446744073709551552))) s = kq2 /\
        word_subword (read YMM0_SSE s) (0,128) = simd4 word_add kq1 a4 /\
        word_subword (read YMM1_SSE s) (0,128) =
          ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
        word_subword (read YMM2_SSE s) (0,128) =
          CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
        word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
        word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
        word_subword (read YMM5_SSE s) (0,128) = (m2r:int128) /\
        word_subword (read YMM7_SSE s) (0,128) =
          (word 16018520953223639909183530438118932995 : int128)` THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s2" THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
    REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC(REWRITE_RULE[SOME_FLAGS]
        SHA256_COMPRESS_HW_GROUP_STEP4_G1_PACKED_BL)]);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP4_FULL_S_G1_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP4_FULL_S_G1_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP4_FULL_S_G1_BL)));;

let SHA256_COMPRESS_HW_GROUP_STEP4_G2_RAW_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP_STEP4_G2_RAW),

  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s5" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s6" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s7" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s8" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC SHA256_RNDS2_WK_CONG THEN CONJ_TAC THEN
      CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC) THEN
  TRY REFL_TAC);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP_STEP4_G2_RAW_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP_STEP4_G2_RAW_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP_STEP4_G2_RAW_BL)));;

let SHA256_COMPRESS_HW_GROUP_STEP4_G2_PACKED_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP_STEP4_G2_PACKED),

  let GA = CONV_RULE(TOP_DEPTH_CONV let_CONV)
             (SPECL [`l:int32 list`; `wk:int128`] SHA256_RNDS2_GROUP_ADVANCE) in
  let GA1 = CONJUNCT1 GA and GA2 = CONJUNCT2 GA in
  let ATCF = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`l:int32 list`;
             `word_subword wk (0,32):int32`; `word_subword wk (32,32):int32`;
             `word_subword wk (64,32):int32`; `word_subword wk (96,32):int32`]
            ABEF_TWO_IS_CDGH_FOUR) in
  REPEAT GEN_TAC THEN REWRITE_TAC[CR4] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA2] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM ATCF] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA1] THEN
  MATCH_ACCEPT_TAC SHA256_COMPRESS_HW_GROUP_STEP4_G2_RAW_BL);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP_STEP4_G2_PACKED_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP_STEP4_G2_PACKED_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP_STEP4_G2_PACKED_BL)));;

let SHA256_COMPRESS_HW_GROUP4_FULL_S_G2_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP4_FULL_S_G2),

  let LANE = WORD_BLAST
    `word_bytereverse (w:int32) =
       (word_join:byte->24 word->int32) (word_subword w (0,8))
        ((word_join:byte->16 word->24 word) (word_subword w (8,8))
         ((word_join:byte->8 word->16 word) (word_subword w (16,8))
          (word_subword w (24,8))))` in
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0xa7`
   `\s. read RCX s = kptr /\
        read (memory :> bytes128 (word_add kptr (word 18446744073709551584))) s = kq3 /\
        word_subword (read YMM0_SSE s) (0,128) = simd4 word_add kq2 a5 /\
        word_subword (read YMM1_SSE s) (0,128) =
          ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
        word_subword (read YMM2_SSE s) (0,128) =
          CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
        word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
        word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
        word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
        word_subword (read YMM6_SSE s) (0,128) =
          (usimd4 word_bytereverse m3r : int128)` THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s2" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s3" THEN
    ENSURES_FINAL_STATE_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
    REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY REFL_TAC THEN
    TRY(REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
        CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC) THEN
    TRY(REWRITE_TAC[usimd4; usimd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
        CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
        GEN_REWRITE_TAC (DEPTH_CONV) [LANE] THEN
        CONV_TAC WORD_REDUCE_CONV THEN
        CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        CONV_TAC WORD_BLAST);
    MATCH_ACCEPT_TAC(REWRITE_RULE[SOME_FLAGS]
        SHA256_COMPRESS_HW_GROUP_STEP4_G2_PACKED_BL)]);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP4_FULL_S_G2_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP4_FULL_S_G2_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP4_FULL_S_G2_BL)));;

let SHA256_COMPRESS_HW_EXIT_BL = prove
 (bl_of_stmt_reg (concl SHA256_COMPRESS_HW_EXIT),

  REPEAT GEN_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s5" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s6" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s7" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WQUAD] THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REPEAT CONJ_TAC THEN TRY REFL_TAC THEN CONV_TAC WORD_BLAST);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_EXIT_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_EXIT_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_EXIT_BL)));;

let SHA256_COMPRESS_HW_JNE_FALLTHRU_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_JNE_FALLTHRU),

  REPEAT GEN_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_JNE_FALLTHRU_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_JNE_FALLTHRU_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_JNE_FALLTHRU_BL)));;

let SHA256_COMPRESS_HW_GROUP_STEP4_G15_RAW_PLUS_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP_STEP4_G15_RAW_PLUS),

  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s5" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s6" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC SHA256_RNDS2_WK_CONG THEN CONJ_TAC THEN
      CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC) THEN
  TRY REFL_TAC);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP_STEP4_G15_RAW_PLUS_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP_STEP4_G15_RAW_PLUS_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP_STEP4_G15_RAW_PLUS_BL)));;

let SHA256_COMPRESS_HW_FEEDFWD_PLUS_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_FEEDFWD_PLUS),

  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s2" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  TRY REFL_TAC);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_FEEDFWD_PLUS_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_FEEDFWD_PLUS_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_FEEDFWD_PLUS_BL)));;

let SHA256_COMPRESS_HW_GROUP4_G15_KLOAD_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP4_G15_KLOAD),

  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s2" THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[]);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP4_G15_KLOAD_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP4_G15_KLOAD_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP4_G15_KLOAD_BL)));;

let SHA256_COMPRESS_HW_GROUP_STEP4_G14_RAW_PLUS_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP_STEP4_G14_RAW_PLUS),

  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s5" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC SHA256_RNDS2_WK_CONG THEN CONJ_TAC THEN
      CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC) THEN
  TRY REFL_TAC);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP_STEP4_G14_RAW_PLUS_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP_STEP4_G14_RAW_PLUS_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP_STEP4_G14_RAW_PLUS_BL)));;

let SHA256_COMPRESS_HW_GROUP_STEP4_G14_PACKED_PLUS_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP_STEP4_G14_PACKED_PLUS),

  let GA = CONV_RULE(TOP_DEPTH_CONV let_CONV)
             (SPECL [`l:int32 list`; `wk:int128`] SHA256_RNDS2_GROUP_ADVANCE) in
  let GA1 = CONJUNCT1 GA and GA2 = CONJUNCT2 GA in
  let ATCF = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`l:int32 list`;
             `word_subword wk (0,32):int32`; `word_subword wk (32,32):int32`;
             `word_subword wk (64,32):int32`; `word_subword wk (96,32):int32`]
            ABEF_TWO_IS_CDGH_FOUR) in
  REPEAT GEN_TAC THEN REWRITE_TAC[CR4] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA2] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM ATCF] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA1] THEN
  MATCH_ACCEPT_TAC SHA256_COMPRESS_HW_GROUP_STEP4_G14_RAW_PLUS_BL);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP_STEP4_G14_PACKED_PLUS_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP_STEP4_G14_PACKED_PLUS_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP_STEP4_G14_PACKED_PLUS_BL)));;

let SHA256_COMPRESS_HW_GROUP4_FULL_S_G14_PLUS_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_GROUP4_FULL_S_G14_PLUS),

  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x2ce`
   `\s. read RCX s = kptr /\
        read (memory :> bytes128 (word_add kptr (word 352))) s = kq1 /\
        word_subword (read YMM0_SSE s) (0,128) = simd4 word_add kq a5 /\
        word_subword (read YMM1_SSE s) (0,128) =
          ABEF_PACK (EL 0 l) (EL 1 l) (EL 4 l) (EL 5 l) /\
        word_subword (read YMM2_SSE s) (0,128) =
          CDGH_PACK (EL 2 l) (EL 3 l) (EL 6 l) (EL 7 l) /\
        word_subword (read YMM3_SSE s) (0,128) = (a3:int128) /\
        word_subword (read YMM4_SSE s) (0,128) = (a4:int128) /\
        word_subword (read YMM5_SSE s) (0,128) = (a5:int128) /\
        word_subword (read YMM6_SSE s) (0,128) = (a6:int128) /\
        word_subword (read YMM8_SSE s) (0,128) = (mask:int128)` THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s2" THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
    REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC(REWRITE_RULE[SOME_FLAGS]
        SHA256_COMPRESS_HW_GROUP_STEP4_G14_PACKED_PLUS_BL)]);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_GROUP4_FULL_S_G14_PLUS_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP4_FULL_S_G14_PLUS_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_GROUP4_FULL_S_G14_PLUS_BL)));;

let SHA256_COMPRESS_HW_JNE_BR_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_JNE_BR),

  REPEAT GEN_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

Printf.printf "BLPORT SHA256_COMPRESS_HW_JNE_BR_BL hyps=%d frees=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_JNE_BR_BL)) (List.length(frees(concl SHA256_COMPRESS_HW_JNE_BR_BL)));;
(* ========================================================================== *)
(* Session 061 — bl_tmc cone-port: the 5 gen_group_038 steady groups G8-G12.  *)
(*                                                                            *)
(* gen_group_038 (L3793) RE-PROVES a steady group by retargeting a rotation   *)
(* template's conclusion (PC/K-disp subst) and REPLAYING a PC-agnostic tactic  *)
(* that hard-codes SHA256_COMPRESS_HW_EXEC.  The _BL port rebuilds the three   *)
(* tactics with EXEC -> BL_EXEC and points the template arrays at the _BL      *)
(* rotation atoms (committed above); the code-agnostic retarget/pcoff/b128/    *)
(* aligned/seamq helpers are reused verbatim.  G8-G12 use the SAME parameter   *)
(* rows as L3806-3810.                                                        *)
(* ========================================================================== *)

let sm_raw_tmpl_038_bl = [| SHA256_COMPRESS_HW_GROUP_STEP4_SM_BL;
                            SHA256_COMPRESS_HW_GROUP_STEP4_SM_R1_BL;
                            SHA256_COMPRESS_HW_GROUP_STEP4_SM_R2_BL;
                            SHA256_COMPRESS_HW_GROUP_STEP4_SM_R3_BL |];;
let sm_pk_tmpl_038_bl  = [| SHA256_COMPRESS_HW_GROUP_STEP4_SM_PACKED_BL;
                            SHA256_COMPRESS_HW_GROUP_STEP4_SM_R1_PACKED_BL;
                            SHA256_COMPRESS_HW_GROUP_STEP4_SM_R2_PACKED_BL;
                            SHA256_COMPRESS_HW_GROUP_STEP4_SM_R3_PACKED_BL |];;
let full_tmpl_038_bl   = [| SHA256_COMPRESS_HW_GROUP4_FULL_S_BL;
                            SHA256_COMPRESS_HW_GROUP4_FULL_S_R1_BL;
                            SHA256_COMPRESS_HW_GROUP4_FULL_S_R2_BL;
                            SHA256_COMPRESS_HW_GROUP4_FULL_S_R3_BL |];;

let sm_raw_tac_038_bl =
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s2" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s3" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s4" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s5" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s6" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s7" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s8" THEN
  X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s9" THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
  REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC SHA256_RNDS2_WK_CONG THEN CONJ_TAC THEN
      CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REFL_TAC) THEN
  TRY REFL_TAC;;
let sm_pk_tac_038_bl raw_thm =
  let GA = CONV_RULE(TOP_DEPTH_CONV let_CONV)
             (SPECL [`l:int32 list`; `wk:int128`] SHA256_RNDS2_GROUP_ADVANCE) in
  let GA1 = CONJUNCT1 GA and GA2 = CONJUNCT2 GA in
  let ATCF = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [`l:int32 list`;
             `word_subword wk (0,32):int32`; `word_subword wk (32,32):int32`;
             `word_subword wk (64,32):int32`; `word_subword wk (96,32):int32`]
            ABEF_TWO_IS_CDGH_FOUR) in
  REPEAT GEN_TAC THEN REWRITE_TAC[CR4] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA2] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM ATCF] THEN
  GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [GSYM GA1] THEN
  MATCH_ACCEPT_TAC raw_thm;;
let full_tac_038_bl gs seamQ pk_thm =
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC (pcoff_038 gs) seamQ THEN CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s1" THEN
    X86_VERBOSE_STEP_TAC SHA256_COMPRESS_HW_BL_EXEC "s2" THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[simd4; simd2] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE READ_YMM_SSE_EQUIV) THEN
    REWRITE_TAC READ_YMM_SSE_EQUIV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC(REWRITE_RULE[SOME_FLAGS] pk_thm)];;

(* per-group generator (bl): identical to gen_group_038 but with the _bl
   templates + tactics; retarget/pcoff/b128/aligned/seamq helpers reused. *)
let gen_group_038_bl r (ge,gs,gx) (gdc,gdn) =
  let (te,ts,tx) = tmpl_pcs_038.(r) and (tdc,tdn) = tmpl_disp_038.(r) in
  let sm_raw = prove(retarget_concl_038 (retarget_sm_038 (ts,tx) (gs,gx)) sm_raw_tmpl_038_bl.(r),
                     sm_raw_tac_038_bl) in
  let sm_pk  = prove(retarget_concl_038 (retarget_sm_038 (ts,tx) (gs,gx)) sm_pk_tmpl_038_bl.(r),
                     sm_pk_tac_038_bl sm_raw) in
  let seamQ  = subst (retarget_seam_038 tdn gdn) seamq_tmpl_038.(r) in
  let full   = prove(retarget_concl_038 (retarget_full_038 (te,tx) (tdc,tdn) (ge,gx) (gdc,gdn))
                          full_tmpl_038_bl.(r),
                     full_tac_038_bl gs seamQ sm_pk) in
  (sm_raw, sm_pk, full);;

let (_,_,SHA256_COMPRESS_HW_GROUP4_FULL_S_G8_BL)  = gen_group_038_bl 0 (0x1a7,0x1b3,0x1d7) (128,160);;
let (_,_,SHA256_COMPRESS_HW_GROUP4_FULL_S_G9_BL)  = gen_group_038_bl 1 (0x1d7,0x1e3,0x207) (160,192);;
let (_,_,SHA256_COMPRESS_HW_GROUP4_FULL_S_G10_BL) = gen_group_038_bl 2 (0x207,0x213,0x237) (192,224);;
let (_,_,SHA256_COMPRESS_HW_GROUP4_FULL_S_G11_BL) = gen_group_038_bl 3 (0x237,0x243,0x267) (224,256);;
let (_,_,SHA256_COMPRESS_HW_GROUP4_FULL_S_G12_BL) = gen_group_038_bl 0 (0x267,0x273,0x297) (256,288);;

Printf.printf "S061_G8_12_BL: G8=%d G9=%d G10=%d G11=%d G12=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_GROUP4_FULL_S_G8_BL))
  (List.length(hyp SHA256_COMPRESS_HW_GROUP4_FULL_S_G9_BL))
  (List.length(hyp SHA256_COMPRESS_HW_GROUP4_FULL_S_G10_BL))
  (List.length(hyp SHA256_COMPRESS_HW_GROUP4_FULL_S_G11_BL))
  (List.length(hyp SHA256_COMPRESS_HW_GROUP4_FULL_S_G12_BL));;

(* ========================================================================== *)
(* Session 061 — bl_tmc cone-port: G3 (neg-disp gen) + the head composer pair.*)
(* CORE_HEAD_CRYPTO_BL / CORE_HEAD_BL are the committed builder blocks with    *)
(* every cone-lemma ref X -> X_BL and execup -> execup_bl; the composed        *)
(* comp_concl is rebuilt from the _BL sub-lemmas (already carries bl_tmc, so    *)
(* no bl_of_stmt).  G3 reuses the _bl generator helpers from the block above.  *)
(* Validated hyps=0 on s055cold. Template = nohw sha256_compress.ml L10955+.   *)
(* ========================================================================== *)
(* ===== s061 bl-port: G3 + head composer pair (CORE_HEAD_CRYPTO, CORE_HEAD) ===== *)

let G3_SM_RAW_BL =
  prove(retarget_concl_038 g3_sm_sub sm_raw_tmpl_038_bl.(3), sm_raw_tac_038_bl);;
let G3_SM_PACKED_BL =
  prove(retarget_concl_038 g3_sm_sub sm_pk_tmpl_038_bl.(3), sm_pk_tac_038_bl G3_SM_RAW_BL);;
let SHA256_COMPRESS_HW_GROUP4_FULL_S_G3_BL =
  prove(retarget_concl_038 g3_full_sub full_tmpl_038_bl.(3),
        full_tac_038_bl 0xd0 g3_seamQ G3_SM_PACKED_BL);;
Printf.printf "S061_G3_BL hyps=%d\n%!" (List.length(hyp SHA256_COMPRESS_HW_GROUP4_FULL_S_G3_BL));;

(* -- self-contained helpers -- *)
let hc_strip_atom th =
  let bod = snd(strip_forall(concl th)) in
  let ens = if is_imp bod then snd(dest_imp bod) else bod in
  let l,c = dest_comb ens in let l2,q = dest_comb l in let _,p = dest_comb l2 in (p,q,c);;
let hc_conjs_of_lam q = let s,body = dest_abs q in s, conjuncts body;;
let hc_contains s sub =
  let ls=String.length s and lsub=String.length sub in
  let rec go i = i+lsub<=ls && (String.sub s i lsub = sub || go(i+1)) in go 0;;
let hc_find sub cs = find (fun c -> hc_contains (string_of_term c) sub) cs;;
let hc_ymm post nm =
  let _,cs = hc_conjs_of_lam post in
  snd(dest_eq(find (fun c -> is_eq c
        && hc_contains (string_of_term(fst(dest_eq c))) nm) cs));;
let hc_list_of_abef post =
  let y = hc_ymm post "YMM1_SSE" in rand(rand(rator(rator(rator y))));;

let vG0 = SHA256_COMPRESS_HW_GROUP4_FULL_S_G0_BL;;
let vG1 = SHA256_COMPRESS_HW_GROUP4_FULL_S_G1_BL;;
let vG2 = SHA256_COMPRESS_HW_GROUP4_FULL_S_G2_BL;;
let vG3 = SHA256_COMPRESS_HW_GROUP4_FULL_S_G3_BL;;

(* ---- g0: keep binders free (canonical), read its post ---- *)
let g0th = SPEC_ALL vG0;;
let (pg0,qg0,cg0) = hc_strip_atom g0th;;
let svar, pg0c = hc_conjs_of_lam pg0;;               (* canonical state var *)
let canon src cs = let s,_ = src in map (vsubst[svar,s]) cs;;
let _,qg0c0 = hc_conjs_of_lam qg0;; let qg0_svar,_ = hc_conjs_of_lam qg0;;
let qg0c = map (vsubst[svar,qg0_svar]) qg0c0;;
let l1     = hc_list_of_abef qg0;;                   (* CR4 l (simd4 add kq0 a3) *)
let w1     = hc_ymm qg0 "YMM4_SSE";;                 (* usimd4 word_bytereverse m1r *)
let ymm9v  = vsubst[svar,qg0_svar] (hc_find "YMM9_SSE"  qg0c0);;
let ymm10v = vsubst[svar,qg0_svar] (hc_find "YMM10_SSE" qg0c0);;

(* ---- g1: SPECL to g0's post occupants ---- *)
let g1th = SPECL [`pc:num`;`kbase:num`;`kptr:int64`;`dptr:int64`;
                  l1; `kq1:int128`;`kq2:int128`; `a3:int128`; w1; `m2r:int128`] vG1;;
let (pg1,qg1,cg1) = hc_strip_atom g1th;;
let sg1,pg1c0 = hc_conjs_of_lam pg1;; let pg1c = canon (sg1,()) pg1c0;;
let sq1,qg1c0 = hc_conjs_of_lam qg1;; let qg1c = map (vsubst[svar,sq1]) qg1c0;;
let l2     = hc_list_of_abef qg1;;
let g1_y3  = hc_ymm qg1 "YMM3_SSE";;                 (* sha256_msg1 a3 w1 *)
let w2     = hc_ymm qg1 "YMM5_SSE";;                 (* usimd4 word_bytereverse m2r *)
let rsi_post = vsubst[svar,sq1] (hc_find "read RSI" qg1c0);;   (* RSI = dptr+0x40 *)

(* ---- g2: SPECL to g1's post occupants ---- *)
let g2th = SPECL [`pc:num`;`kbase:num`;`kptr:int64`;
                  l2; `kq2:int128`;`kq3:int128`; g1_y3; w1; w2; `m3r:int128`] vG2;;
let (pg2,qg2,cg2) = hc_strip_atom g2th;;
let sg2,pg2c0 = hc_conjs_of_lam pg2;; let pg2c = canon (sg2,()) pg2c0;;
let sq2,qg2c0 = hc_conjs_of_lam qg2;; let qg2c = map (vsubst[svar,sq2]) qg2c0;;
let l3     = hc_list_of_abef qg2;;
let g2_y3  = hc_ymm qg2 "YMM3_SSE";;
let g2_y4  = hc_ymm qg2 "YMM4_SSE";;                 (* sha256_msg1 w1 w2 *)
let g2_y5  = hc_ymm qg2 "YMM5_SSE";;                 (* w2 (held) *)
let g2_y6  = hc_ymm qg2 "YMM6_SSE";;                 (* usimd4 word_bytereverse m3r (=w3) *)

(* ---- g3: SPECL to g2's post occupants ---- *)
let g3th = SPECL [`pc:num`;`kbase:num`;`kptr:int64`;
                  l3; `kq3:int128`;`kq4:int128`; g2_y3; g2_y4; g2_y5; g2_y6] vG3;;
let (pg3,qg3,cg3) = hc_strip_atom g3th;;
let sg3,pg3c0 = hc_conjs_of_lam pg3;; let pg3c = canon (sg3,()) pg3c0;;
let sq3,qg3c0 = hc_conjs_of_lam qg3;; let qg3c = map (vsubst[svar,sq3]) qg3c0;;

(* ---- carried read-only conjuncts (canonical state var) ---- *)
let rsi_pre  = hc_find "read RSI"  pg1c;;            (* RSI = dptr *)
let ymm5_m2r = hc_find "YMM5_SSE"  pg1c;;            (* YMM5 = m2r *)
let ymm6_m3r = hc_find "YMM6_SSE"  pg2c;;            (* YMM6 = m3r *)
let kq2_read = hc_find "(word 18446744073709551552)" pg1c;;   (* kq2 @ -64  *)
let kq3_read = hc_find "(word 18446744073709551584)" pg2c;;   (* kq3 @ -32  *)
let kq4_read = hc_find "bytes128 kptr)" pg3c;;                 (* kq4 @ 0    *)

(* ---- composed PRE = g0.pre + {RSI=dptr, YMM5=m2r, YMM6=m3r, kq2,kq3,kq4} ---- *)
let pre_lam = mk_abs(svar,
  list_mk_conj (pg0c @ [rsi_pre; ymm5_m2r; ymm6_m3r; kq2_read; kq3_read; kq4_read]));;

(* ---- composed POST = g3.post + {RSI=dptr+0x40, YMM9, YMM10} ---- *)
let post_lam = mk_abs(svar, list_mk_conj (qg3c @ [rsi_post; ymm9v; ymm10v]));;

(* ---- composed FRAME = union of all four ---- *)
let comp_frame =
 `MAYCHANGE [RIP; RSI] ,,
  MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM5_SSE;
             YMM6_SSE; YMM7_SSE; YMM9_SSE; YMM10_SSE] ,,
  MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;

(* ---- hyps: aligned on each consumed K quad ---- *)
let comp_hyps = list_mk_conj
 [`aligned 16 (word_add (kptr:int64) (word 18446744073709551488))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551520))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551552))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551584))`];;

let ens_head = rator(rator(rator(snd(dest_imp(snd(strip_forall(concl vG0)))))));;
let mk_ensures p q c = mk_comb(mk_comb(mk_comb(ens_head,p),q),c);;
let bvars = [`pc:num`;`kbase:num`;`kptr:int64`;`dptr:int64`;`l:int32 list`;
             `kq0:int128`;`kq1:int128`;`kq2:int128`;`kq3:int128`;`kq4:int128`;
             `a3:int128`;`m1r:int128`;`m2r:int128`;`m3r:int128`];;
let comp_concl =
  list_mk_forall(bvars, mk_imp(comp_hyps, mk_ensures pre_lam post_lam comp_frame));;

(* ---- seams (minus bytes_loaded + read RIP), plus carried facts ---- *)
let keep c = not(hc_contains (string_of_term c) "bytes_loaded")
             && not(hc_contains (string_of_term c) "read RIP");;
let core cs = filter keep cs;;
(* seam@0x76 (before g1) = g1.pre-core + {YMM6=m3r, YMM9, YMM10, kq3, kq4} *)
let seamQ1 = mk_abs(svar,
  list_mk_conj (core pg1c @ [ymm6_m3r; ymm9v; ymm10v; kq3_read; kq4_read]));;
(* seam@0x99 (before g2) = g2.pre-core + {RSI=dptr+0x40, YMM9, YMM10, kq4} *)
let seamQ2 = mk_abs(svar,
  list_mk_conj (core pg2c @ [rsi_post; ymm9v; ymm10v; kq4_read]));;
(* seam@0xc7 (before g3) = g3.pre-core + {RSI=dptr+0x40, YMM9, YMM10} *)
let seamQ3 = mk_abs(svar,
  list_mk_conj (core pg3c @ [rsi_post; ymm9v; ymm10v]));;

Printf.printf "S042_HEADCRYPTO concl built\n%!";;

let SHA256_COMPRESS_HW_CORE_HEAD_CRYPTO_BL = prove
 (comp_concl,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x76` seamQ1 THEN CONJ_TAC THENL
   [MP_TAC(REWRITE_RULE[SOME_FLAGS] g0th) THEN ASM_REWRITE_TAC[] THEN
    ENSURES_SUBLEMMA_TAC execup_bl "s" "s'" THEN ASM_REWRITE_TAC[];
    ENSURES_SEQUENCE_TAC `pc + 0x99` seamQ2 THEN CONJ_TAC THENL
     [MP_TAC(REWRITE_RULE[SOME_FLAGS] g1th) THEN ASM_REWRITE_TAC[] THEN
      ENSURES_SUBLEMMA_TAC execup_bl "s" "s'" THEN ASM_REWRITE_TAC[];
      ENSURES_SEQUENCE_TAC `pc + 0xc7` seamQ3 THEN CONJ_TAC THENL
       [MP_TAC(REWRITE_RULE[SOME_FLAGS] g2th) THEN ASM_REWRITE_TAC[] THEN
        ENSURES_SUBLEMMA_TAC execup_bl "s" "s'" THEN ASM_REWRITE_TAC[];
        MP_TAC(REWRITE_RULE[SOME_FLAGS] g3th) THEN ASM_REWRITE_TAC[] THEN
        ENSURES_SUBLEMMA_TAC execup_bl "s" "s'" THEN ASM_REWRITE_TAC[]]]]);;

Printf.printf "S042_CORE_HEAD_CRYPTO hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_CORE_HEAD_CRYPTO_BL))
  (List.length (frees (concl SHA256_COMPRESS_HW_CORE_HEAD_CRYPTO_BL)));;
Printf.printf "S042_HEADCRYPTO_DONE\n%!";;
(* ========================================================================= *)
(* Session 042 -- CORE_HEAD: ENTRY_REPACK ; HEAD_MSGLOAD0 ; CORE_HEAD_CRYPTO   *)
(* composed into the full head segment (pc+0x07 -> pc+0xf4).                   *)
(*                                                                            *)
(* Two distinct pointers: RDI = sptr (state array, read at ENTRY -> q0,q1),   *)
(* RSI = mptr (message block, read at MSGLOAD -> m0..m3, advanced by g1's lea).*)
(* ENTRY's abstract byteswap-mask binder is INSTANTIATED to the concrete       *)
(* rodata literal so it matches HEAD_MSGLOAD0's YMM7 requirement.  CRYPTO's     *)
(* working list l is instantiated to the 8 state words (word_subword q0/q1)    *)
(* and EL_CONV-reduced so its ABEF/CDGH_PACK(EL k l) pre matches ENTRY's post.  *)
(*                                                                            *)
(* Read-only riders (validated in the g0;g1 de-risk + CORE_HEAD_CRYPTO):       *)
(*   - RSI=mptr + the 4 message memory reads ride through ENTRY (RSI, memory   *)
(*     not in ENTRY's frame) to feed MSGLOAD.                                  *)
(*   - the 5 K memory reads ride through ENTRY+MSGLOAD to feed CRYPTO.          *)
(*   - YMM1/YMM2 (ENTRY's ABEF/CDGH pack) ride read-only through MSGLOAD.       *)
(*   - RDI=sptr rides read-only through ALL of MSGLOAD+CRYPTO (hook for the     *)
(*     Phase-5 exit state store) into the composed post.                       *)
(* All three legs are non-reflexive (each seam strictly extends the sub-       *)
(* lemma's pre by carried riders) -> stock ENSURES_SUBLEMMA_TAC.               *)
(* ========================================================================= *)


let ch_strip_atom th =
  let bod = snd(strip_forall(concl th)) in
  let ens = if is_imp bod then snd(dest_imp bod) else bod in
  let l,c = dest_comb ens in let l2,q = dest_comb l in let _,p = dest_comb l2 in (p,q,c);;
let ch_conjs q = let s,body = dest_abs q in s, conjuncts body;;
let ch_contains s sub =
  let ls=String.length s and lsub=String.length sub in
  let rec go i = i+lsub<=ls && (String.sub s i lsub = sub || go(i+1)) in go 0;;
let ch_find sub cs = find (fun c -> ch_contains (string_of_term c) sub) cs;;

(* concrete instantiation atoms *)
let masklit = `word 16018520953223639909183530438118932995 : int128`;;
let brm0 = `usimd4 word_bytereverse (m0:int128) : int128`;;
let stlist =
  `[(word_subword (q0:int128) (0,32):int32); (word_subword (q0:int128) (32,32):int32);
    (word_subword (q0:int128) (64,32):int32); (word_subword (q0:int128) (96,32):int32);
    (word_subword (q1:int128) (0,32):int32); (word_subword (q1:int128) (32,32):int32);
    (word_subword (q1:int128) (64,32):int32); (word_subword (q1:int128) (96,32):int32)]`;;

(* -- instantiated sub-lemmas -- *)
let entry_i = SPECL [`pc:num`;`kbase:num`;`kptr:int64`;`sptr:int64`;
                     `q0:int128`;`q1:int128`; masklit] SHA256_COMPRESS_HW_ENTRY_REPACK_BL;;
let msg_i   = SPECL [`pc:num`;`kbase:num`;`kptr:int64`;`mptr:int64`;
                     `m0:int128`;`m1:int128`;`m2:int128`;`m3:int128`]
                SHA256_COMPRESS_HW_HEAD_MSGLOAD0_BL;;
let crypto_i0 = SPECL [`pc:num`;`kbase:num`;`kptr:int64`;`mptr:int64`; stlist;
                       `kq0:int128`;`kq1:int128`;`kq2:int128`;`kq3:int128`;`kq4:int128`;
                       brm0; `m1:int128`;`m2:int128`;`m3:int128`]
                  SHA256_COMPRESS_HW_CORE_HEAD_CRYPTO_BL;;
let crypto_i = CONV_RULE(DEPTH_CONV EL_CONV) crypto_i0;;

(* -- canonical state var = ENTRY.pre's -- *)
let (peE,poE,frE) = ch_strip_atom entry_i;;
let sv, peEc = ch_conjs peE;;
let rebase src cs = let s,_ = ch_conjs src in map (vsubst[sv,s]) cs;;
let poEc = rebase poE (snd(ch_conjs poE));;
let (peM,poM,frM) = ch_strip_atom msg_i;;
let peMc = rebase peM (snd(ch_conjs peM));;
let poMc = rebase poM (snd(ch_conjs poM));;
let (peC,poC,frC) = ch_strip_atom crypto_i;;
let peCc = rebase peC (snd(ch_conjs peC));;
let poCc = rebase poC (snd(ch_conjs poC));;

(* -- key carried facts (canonical sv) -- *)
let rdi_fact  = ch_find "read RDI" poEc;;                (* RDI = sptr (ENTRY post) *)
let rsi_pre   = ch_find "read RSI" peMc;;                (* RSI = mptr *)
let ymm1_pack = ch_find "YMM1_SSE" poEc;;                (* ABEF_PACK(q0..) *)
let ymm2_pack = ch_find "YMM2_SSE" poEc;;                (* CDGH_PACK(q0..) *)
let msg_reads = filter (fun c -> ch_contains (string_of_term c) "read (memory"
                   && ch_contains (string_of_term c) "mptr") peMc;;
let k_reads = filter (fun c -> ch_contains (string_of_term c) "read (memory"
                 && (ch_contains (string_of_term c) "bytes128 kptr)"
                     || ch_contains (string_of_term c) "18446744073709551")) peCc;;

Printf.printf "S042_CH counts: msg_reads=%d k_reads=%d\n%!"
  (List.length msg_reads) (List.length k_reads);;

(* -- composed PRE = ENTRY.pre + {RSI=mptr, 4 msg reads, 5 K reads} -- *)
let pre_lam = mk_abs(sv, list_mk_conj (peEc @ [rsi_pre] @ msg_reads @ k_reads));;

(* -- composed POST = CRYPTO.post + {RDI=sptr} -- *)
let post_lam = mk_abs(sv, list_mk_conj (poCc @ [rdi_fact]));;

(* -- composed FRAME = union ENTRY {YMM0/1/2/7/8} + MSG {YMM3/4/5/6} +          *)
(*    CRYPTO {RSI,YMM0..7,9,10,flags} -- *)
let comp_frame =
 `MAYCHANGE [RIP; RSI] ,,
  MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM5_SSE;
             YMM6_SSE; YMM7_SSE; YMM8_SSE; YMM9_SSE; YMM10_SSE] ,,
  MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;

(* -- hyps: ENTRY's aligned(kptr+384) + CRYPTO's 4 neg-disp aligned -- *)
let comp_hyps = list_mk_conj
 [`aligned 16 (word_add (kptr:int64) (word 384))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551488))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551520))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551552))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551584))`];;

let ens_head = rator(rator(rator(snd(dest_imp(snd(strip_forall(concl
                 SHA256_COMPRESS_HW_ENTRY_REPACK_BL)))))));;
let mk_ensures p q c = mk_comb(mk_comb(mk_comb(ens_head,p),q),c);;
let bvars = [`pc:num`;`kbase:num`;`kptr:int64`;`sptr:int64`;`mptr:int64`;
             `q0:int128`;`q1:int128`;`m0:int128`;`m1:int128`;`m2:int128`;`m3:int128`;
             `kq0:int128`;`kq1:int128`;`kq2:int128`;`kq3:int128`;`kq4:int128`];;
let comp_concl =
  list_mk_forall(bvars, mk_imp(comp_hyps, mk_ensures pre_lam post_lam comp_frame));;

(* -- seams (minus bytes_loaded + read RIP) -- *)
let keep c = not(ch_contains (string_of_term c) "bytes_loaded")
             && not(ch_contains (string_of_term c) "read RIP");;
let core cs = filter keep cs;;
(* seam1@0x38 = MSGLOAD.pre-core + {YMM1,YMM2 (ENTRY), 5 K reads, RDI=sptr} *)
let seamQ1 = mk_abs(sv,
  list_mk_conj (core peMc @ [ymm1_pack; ymm2_pack] @ k_reads @ [rdi_fact]));;
(* seam2@0x50 = CRYPTO.pre-core + {RDI=sptr} *)
let seamQ2 = mk_abs(sv, list_mk_conj (core peCc @ [rdi_fact]));;

Printf.printf "S042_CH concl built\n%!";;

let SHA256_COMPRESS_HW_CORE_HEAD_BL = prove
 (comp_concl,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x38` seamQ1 THEN CONJ_TAC THENL
   [(* leg 1: ENTRY_REPACK[mask:=lit] *)
    MP_TAC entry_i THEN ASM_REWRITE_TAC[] THEN
    ENSURES_SUBLEMMA_TAC execup_bl "s" "s'" THEN ASM_REWRITE_TAC[];
    ENSURES_SEQUENCE_TAC `pc + 0x50` seamQ2 THEN CONJ_TAC THENL
     [(* leg 2: HEAD_MSGLOAD0 *)
      MP_TAC msg_i THEN ASM_REWRITE_TAC[] THEN
      ENSURES_SUBLEMMA_TAC execup_bl "s" "s'" THEN ASM_REWRITE_TAC[];
      (* leg 3: CORE_HEAD_CRYPTO[l:=state words, EL-reduced] *)
      MP_TAC(REWRITE_RULE[SOME_FLAGS] crypto_i) THEN ASM_REWRITE_TAC[] THEN
      ENSURES_SUBLEMMA_TAC execup_bl "s" "s'" THEN ASM_REWRITE_TAC[]]]);;

Printf.printf "S042_CORE_HEAD hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_CORE_HEAD_BL))
  (List.length (frees (concl SHA256_COMPRESS_HW_CORE_HEAD_BL)));;
Printf.printf "S042_COREHEAD_DONE\n%!";;
(* ===== s061 bl-port: CORE_TAIL3 (tail composer G13;G14;G15;FEEDFWD@0x297->0x302) ===== *)
let strip_atom th =
  let bod = snd(strip_forall(concl th)) in
  let ens = if is_imp bod then snd(dest_imp bod) else bod in
  let l,c = dest_comb ens in
  let l2,q = dest_comb l in
  let _,p = dest_comb l2 in (p,q,c);;
let vbyname th n = find (fun v -> name_of v = n) (fst(strip_forall(concl th)));;
let conjs_of_lam q = let s,body = dest_abs q in s, conjuncts body;;
let contains s sub =
  let ls=String.length s and lsub=String.length sub in
  let rec go i = i+lsub<=ls && (String.sub s i lsub = sub || go(i+1)) in go 0;;
let is_kread off c =
  is_eq c && contains (string_of_term c) "bytes128"
          && contains (string_of_term c) ("(word " ^ off ^ ")");;
let kread_for s src_svar src_conjs off =
  vsubst[s,src_svar] (find (is_kread off) src_conjs);;

(* Instantiate a FULL tail atom's ring binders (l,a3,a4,a5,a6) to prev post.    *)
let ymm_rhs post nm =
  let _,cs = conjs_of_lam post in
  let hit = find (fun c -> is_eq c && contains (string_of_term(fst(dest_eq c))) nm) cs in
  snd(dest_eq hit);;
let list_of_abef post =
  let ymm1 = ymm_rhs post "YMM1_SSE" in
  rand(rand(rator(rator(rator ymm1))));;
let post_ring q =
  (list_of_abef q, ymm_rhs q "YMM3_SSE", ymm_rhs q "YMM4_SSE",
   ymm_rhs q "YMM5_SSE", ymm_rhs q "YMM6_SSE");;
let inst_ring atomthm l_v a3_v a4_v a5_v a6_v =
  INST [ l_v,  vbyname atomthm "l";  a3_v, vbyname atomthm "a3";
         a4_v, vbyname atomthm "a4"; a5_v, vbyname atomthm "a5";
         a6_v, vbyname atomthm "a6" ] (SPEC_ALL atomthm);;

(* G13/G14/G15 all name their K-quads generically kq (consumed) / kq1 (next),   *)
(* unlike the s037 R-atoms which had distinct kq_i names.  So rename them to     *)
(* distinct kq0/kq1/kq2 by INST of the literal vars on the SPEC_ALL result       *)
(* (vbyname after SPEC_ALL fails -- no binders left).                            *)
let inst_ring_kq atomthm kmap l_v a3_v a4_v a5_v a6_v =
  let base = SPEC_ALL atomthm in
  INST (kmap @
        [ l_v,  vbyname atomthm "l";  a3_v, vbyname atomthm "a3";
          a4_v, vbyname atomthm "a4"; a5_v, vbyname atomthm "a5";
          a6_v, vbyname atomthm "a6" ]) base;;

(* ---- g13 (FULL_S_G13): consumes kq0@+288, threads kq1@+320 ---- *)
let vG13 = SHA256_COMPRESS_HW_GROUP4_FULL_S_G13_BL;;
let g13th = INST [`kq0:int128`, `kq:int128`; `kq1:int128`, `kq1:int128`]
                 (SPEC_ALL vG13);;
let (pg13,qg13,cg13) = strip_atom g13th;;
let (l13,a313,a413,a513,a613) = post_ring qg13;;

(* ---- g14 (FULL_S_G14): consumes kq1@+320, threads kq2@+352 ----             *)
(* rename g14's kq (consumed @+320) -> kq1, kq1 (next @+352) -> kq2.            *)
let g14th = inst_ring_kq SHA256_COMPRESS_HW_GROUP4_FULL_S_G14_BL
              [ `kq1:int128`, `kq:int128`; `kq2:int128`, `kq1:int128` ]
              l13 a313 a413 a513 a613;;
let (pg14,qg14,cg14) = strip_atom g14th;;
let (l14,a314,a414,a514,a614) = post_ring qg14;;

(* ---- g15 (FULL_S_G15, terminal): consumes kq2@+352 ---- *)
let g15th = inst_ring_kq SHA256_COMPRESS_HW_GROUP4_FULL_S_G15_BL
              [ `kq2:int128`, `kq:int128` ]
              l14 a314 a414 a514 a614;;
let (pg15,qg15,cg15) = strip_atom g15th;;

(* -- state vars + pre conjunct lists -- *)
let svar13,pg13c = conjs_of_lam pg13;;
let sg14,pg14c = conjs_of_lam pg14;;
let sg15,pg15c = conjs_of_lam pg15;;

(* -- composed FRAME = union of all three (g15 adds RDX; g13/g14 add YMM3..7) -- *)
let full_frame =
  `MAYCHANGE [RIP] ,,
   MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM5_SSE; YMM6_SSE; YMM7_SSE] ,,
   MAYCHANGE [RDX] ,,
   MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;

(* -- composed PRE = g13.pre + the two-ahead kq2@+352 (from g14 pre) -- *)
let pre_extra = [ kread_for svar13 sg14 pg14c "352" ];;
let pre_lam = mk_abs(svar13, list_mk_conj (pg13c @ pre_extra));;
let post_lam = qg15;;

let ens_head = rator(rator(rator(snd(dest_imp(snd(strip_forall(concl vG13)))))));;
let mk_ensures p q c = mk_comb(mk_comb(mk_comb(ens_head,p),q),c);;
let bvars = [`pc:num`;`kbase:num`;`kptr:int64`;`l:int32 list`;
             `kq0:int128`;`kq1:int128`;`kq2:int128`;
             `a3:int128`;`a4:int128`;`a5:int128`;`a6:int128`];;
let hyps = list_mk_conj
  [`aligned 16 (word_add (kptr:int64) (word 288))`;
   `aligned 16 (word_add (kptr:int64) (word 320))`;
   `aligned 16 (word_add (kptr:int64) (word 352))`];;
let comp_concl = list_mk_forall(bvars, mk_imp(hyps, mk_ensures pre_lam post_lam full_frame));;

(* -- seams (minus bytes_loaded+RIP) -- *)
let seam_core pre =
  let s,cs = conjs_of_lam pre in
  let keep c = not(contains (string_of_term c) "bytes_loaded")
               && not(contains (string_of_term c) "read RIP") in
  (s, filter keep cs);;
(* seamQ1 @0x2c2 (before g14): g14.pre + carried kq2@+352 (already in g14.pre!  *)
(* g14.pre reads kq1@+320 and kq2@+352, so it is exactly reflexive here).       *)
let seamQ1 = let s,cs = seam_core pg14 in mk_abs(s, list_mk_conj cs);;
(* seamQ2 @0x2e4 (before g15): g15.pre exactly (reflexive terminal). *)
let seamQ2 = let s,cs = seam_core pg15 in mk_abs(s, list_mk_conj cs);;

(* ------------------------------ THE PROOF ------------------------------ *)
let SHA256_COMPRESS_HW_CORE_TAIL3_BL = prove
 (comp_concl,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x2c2` seamQ1 THEN CONJ_TAC THENL
   [(* leg 1: g13 -- composed pre carries kq2 beyond g13 -> but g13.post threads *)
    (* kq1 only, and seamQ1=g14.pre needs kq1@320+kq2@352; kq2 rides the frame.  *)
    MP_TAC(REWRITE_RULE[SOME_FLAGS] g13th) THEN ASM_REWRITE_TAC[] THEN
    ENSURES_SUBLEMMA_TAC execup_bl "s" "s'" THEN ASM_REWRITE_TAC[];
    ENSURES_SEQUENCE_TAC `pc + 0x2e4` seamQ2 THEN CONJ_TAC THENL
     [(* leg 2: g14 -- seamQ1 == g14.pre exactly, and g14 threads kq2@352 which  *)
      (* is exactly what seamQ2 == g15.pre needs -> nothing rides beyond g14 ->   *)
      (* REFLEXIVE seam (P=>P' collapses to T; stock sublemma's dest_binder fails).*)
      MP_TAC(REWRITE_RULE[SOME_FLAGS] g14th) THEN ASM_REWRITE_TAC[] THEN
      ENSURES_SUBLEMMA_REFL_TAC execup_bl "s" "s'" THEN ASM_REWRITE_TAC[];
      (* leg 3: g15 terminal -- seamQ2 == g15.pre, POST == g15.post -> reflexive *)
      MP_TAC(REWRITE_RULE[SOME_FLAGS] g15th) THEN ASM_REWRITE_TAC[] THEN
      ENSURES_SUBLEMMA_REFL_TAC execup_bl "s" "s'" THEN ASM_REWRITE_TAC[]]]);;

Printf.printf "S039_CORE_TAIL3 hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_CORE_TAIL3_BL))
  (List.length (frees (concl SHA256_COMPRESS_HW_CORE_TAIL3_BL)));;
Printf.printf "S039_TAIL3_DONE\n%!";;
(* ========================================================================= *)
(* Session 062 -- bl_tmc cone-port BATCH 1: the multi-block loop-body deps.    *)
(* SPEC_STEP_G8..G12_BL (steady groups, gen_specstep over the committed _BL     *)
(* group atoms) + HEAD38_RAW_BL/HEAD38_ABS_BL (loop-body head pc+0x38->0xf4).   *)
(* Statements = bl_of_stmt(concl ORIGINAL) (bl-image equivalence free); each     *)
(* aconv-gated against its non-BL original.  These are on the true CORE_CORRECT  *)
(* dependency closure (audit found STATE's single-block composer list wrong).    *)
(* ========================================================================= *)
(* Session 062 — BATCH 1: SPEC_STEP_G8..G12_BL + HEAD38_RAW_BL + HEAD38_ABS_BL. *)
(* Dev/validate on s055cold (all originals + leaf _BL + gen_specstep helpers +   *)
(* bl-infra already bound).  Target statements = bl_of_stmt(concl ORIGINAL)      *)
(* (reviewer approach B: bl-image equivalence is free), each aconv-gated.        *)

(* ---- SPEC_STEP_G8..G12_BL: gen_specstep is pure term-surgery + spec folds;    *)
(* seed with the committed _BL group atom and target bl_of_stmt(concl ORIG).     *)
let mk_specstep_bl orig r atom_bl (ge,gx) (gkc,gkn) =
  prove(bl_of_stmt (concl orig), specstep_tac r atom_bl);;

let SHA256_COMPRESS_HW_SPEC_STEP_G8_BL =
  mk_specstep_bl SHA256_COMPRESS_HW_SPEC_STEP_G8 0
    SHA256_COMPRESS_HW_GROUP4_FULL_S_G8_BL (0x1a7,0x1d7) (128,160);;
let SHA256_COMPRESS_HW_SPEC_STEP_G9_BL =
  mk_specstep_bl SHA256_COMPRESS_HW_SPEC_STEP_G9 1
    SHA256_COMPRESS_HW_GROUP4_FULL_S_G9_BL (0x1d7,0x207) (160,192);;
let SHA256_COMPRESS_HW_SPEC_STEP_G10_BL =
  mk_specstep_bl SHA256_COMPRESS_HW_SPEC_STEP_G10 2
    SHA256_COMPRESS_HW_GROUP4_FULL_S_G10_BL (0x207,0x237) (192,224);;
let SHA256_COMPRESS_HW_SPEC_STEP_G11_BL =
  mk_specstep_bl SHA256_COMPRESS_HW_SPEC_STEP_G11 3
    SHA256_COMPRESS_HW_GROUP4_FULL_S_G11_BL (0x237,0x267) (224,256);;
let SHA256_COMPRESS_HW_SPEC_STEP_G12_BL =
  mk_specstep_bl SHA256_COMPRESS_HW_SPEC_STEP_G12 0
    SHA256_COMPRESS_HW_GROUP4_FULL_S_G12_BL (0x267,0x297) (256,288);;

let ag nm th_bl th_orig =
  let ok = aconv (concl th_bl) (bl_of_stmt(concl th_orig)) in
  Printf.printf "GATE %-30s %s hyps=%d frees=%d\n%!" nm
    (if ok then "PASS" else "*** FAIL ***")
    (List.length(hyp th_bl)) (List.length(frees(concl th_bl)));;
ag "SPEC_STEP_G8_BL"  SHA256_COMPRESS_HW_SPEC_STEP_G8_BL  SHA256_COMPRESS_HW_SPEC_STEP_G8;;
ag "SPEC_STEP_G9_BL"  SHA256_COMPRESS_HW_SPEC_STEP_G9_BL  SHA256_COMPRESS_HW_SPEC_STEP_G9;;
ag "SPEC_STEP_G10_BL" SHA256_COMPRESS_HW_SPEC_STEP_G10_BL SHA256_COMPRESS_HW_SPEC_STEP_G10;;
ag "SPEC_STEP_G11_BL" SHA256_COMPRESS_HW_SPEC_STEP_G11_BL SHA256_COMPRESS_HW_SPEC_STEP_G11;;
ag "SPEC_STEP_G12_BL" SHA256_COMPRESS_HW_SPEC_STEP_G12_BL SHA256_COMPRESS_HW_SPEC_STEP_G12;;

Printf.printf "S062_BATCH1_SPECSTEP_DONE\n%!";;

(* ===== s062 bl-port: HEAD38_RAW_BL (loop-body head pc+0x38->0xf4) ===== *)
let h38_strip_atom th =
  let bod = snd(strip_forall(concl th)) in
  let ens = if is_imp bod then snd(dest_imp bod) else bod in
  let l,c = dest_comb ens in let l2,q = dest_comb l in let _,p = dest_comb l2 in (p,q,c);;
let h38_conjs q = let s,body = dest_abs q in s, conjuncts body;;
let h38_contains s sub =
  let ls=String.length s and lsub=String.length sub in
  let rec go i = i+lsub<=ls && (String.sub s i lsub = sub || go(i+1)) in go 0;;
let h38_find sub cs = find (fun c -> h38_contains (string_of_term c) sub) cs;;

let masklit = `word 16018520953223639909183530438118932995 : int128`;;
let brm0 = `usimd4 word_bytereverse (m0:int128) : int128`;;
let l_state = `l:int32 list`;;

let msg_i = SPECL [`pc:num`;`kbase:num`;`kptr:int64`;`mptr:int64`;
                   `m0:int128`;`m1:int128`;`m2:int128`;`m3:int128`]
              SHA256_COMPRESS_HW_HEAD_MSGLOAD0_BL;;
let crypto_i0 = SPECL [`pc:num`;`kbase:num`;`kptr:int64`;`mptr:int64`; l_state;
                       `kq0:int128`;`kq1:int128`;`kq2:int128`;`kq3:int128`;`kq4:int128`;
                       brm0; `m1:int128`;`m2:int128`;`m3:int128`]
                  SHA256_COMPRESS_HW_CORE_HEAD_CRYPTO_BL;;
let crypto_i = crypto_i0;;

let (peM,poM,frM) = h38_strip_atom msg_i;;
let sv, peMc = h38_conjs peM;;
let rebase src cs = let s,_ = h38_conjs src in map (vsubst[sv,s]) cs;;
let poMc = rebase poM (snd(h38_conjs poM));;
let (peC,poC,frC) = h38_strip_atom crypto_i;;
let peCc = rebase peC (snd(h38_conjs peC));;
let poCc = rebase poC (snd(h38_conjs poC));;

let ymm1_pack = h38_find "YMM1_SSE" peCc;;   (* ABEF_PACK(EL0/1/4/5 l) *)
let ymm2_pack = h38_find "YMM2_SSE" peCc;;   (* CDGH_PACK(EL2/3/6/7 l) *)
let k_reads = filter (fun c -> h38_contains (string_of_term c) "read (memory"
                 && (h38_contains (string_of_term c) "bytes128 kptr)"
                     || h38_contains (string_of_term c) "18446744073709551")) peCc;;

let pre_lam = mk_abs(sv, list_mk_conj (peMc @ [ymm1_pack; ymm2_pack] @ k_reads));;
let post_lam = mk_abs(sv, list_mk_conj poCc);;
let comp_frame =
 `MAYCHANGE [RIP; RSI] ,,
  MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM5_SSE;
             YMM6_SSE; YMM7_SSE; YMM9_SSE; YMM10_SSE] ,,
  MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;
let comp_hyps = list_mk_conj
 [`aligned 16 (word_add (kptr:int64) (word 18446744073709551488))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551520))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551552))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551584))`];;
let ens_head = rator(rator(rator(snd(dest_imp(snd(strip_forall(concl
                 SHA256_COMPRESS_HW_CORE_HEAD_CRYPTO_BL)))))));;
let mk_ensures p q c = mk_comb(mk_comb(mk_comb(ens_head,p),q),c);;
let bvars = [`pc:num`;`kbase:num`;`kptr:int64`;`mptr:int64`;`l:int32 list`;
             `m0:int128`;`m1:int128`;`m2:int128`;`m3:int128`;
             `kq0:int128`;`kq1:int128`;`kq2:int128`;`kq3:int128`;`kq4:int128`];;
let comp_concl = list_mk_forall(bvars, mk_imp(comp_hyps, mk_ensures pre_lam post_lam comp_frame));;

let keep c = not(h38_contains (string_of_term c) "bytes_loaded")
             && not(h38_contains (string_of_term c) "read RIP");;
let core cs = filter keep cs;;
let seamQ1 = mk_abs(sv, list_mk_conj (core peCc));;

let SHA256_COMPRESS_HW_HEAD38_RAW_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_HEAD38_RAW),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x50` seamQ1 THEN CONJ_TAC THENL
   [MP_TAC msg_i THEN ASM_REWRITE_TAC[] THEN
    ENSURES_SUBLEMMA_TAC execup_bl "s" "s'" THEN ASM_REWRITE_TAC[];
    MP_TAC(REWRITE_RULE[SOME_FLAGS] crypto_i) THEN ASM_REWRITE_TAC[] THEN
    ENSURES_SUBLEMMA_TAC execup_bl "s" "s'" THEN ASM_REWRITE_TAC[]]);;

(* ===== s062 bl-port: HEAD38_ABS_BL (opaque-spec restatement) ===== *)
let SHA256_COMPRESS_HW_HEAD38_ABS_BL =
  let e j i = mk_comb(`word_bytereverse:int32->int32`,
      list_mk_comb(`EL:num->(int32)list->int32`,[mk_small_numeral(4*i+j);`m:int32 list`])) in
  let rawquad i = list_mk_comb(`WQUAD:int32->int32->int32->int32->int128`,
                    [e 0 i;e 1 i;e 2 i;e 3 i]) in
  let kc j i = list_mk_comb(`EL:num->(int32)list->int32`,
      [mk_small_numeral(4*i+j);`sha256_constants:int32 list`]) in
  let kquad i = list_mk_comb(`WQUAD:int32->int32->int32->int32->int128`,
                  [kc 0 i;kc 1 i;kc 2 i;kc 3 i]) in
  let subs = [ rawquad 0,`m0:int128`; rawquad 1,`m1:int128`;
               rawquad 2,`m2:int128`; rawquad 3,`m3:int128`;
               kquad 0,`kq0:int128`; kquad 1,`kq1:int128`;
               kquad 2,`kq2:int128`; kquad 3,`kq3:int128` ] in
  let headI = INST subs (SPEC_ALL SHA256_COMPRESS_HW_HEAD38_RAW_BL) in
  let bfold i =
    let br = SPECL [`m:int32 list`; mk_small_numeral i] SHA256_COMPRESS_HW_HEAD_MSG_BRIDGE in
    let br = MP br (ARITH_RULE(mk_comb(mk_comb(`(<):num->num->bool`,mk_small_numeral i),`4`))) in
    CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV) br in
  let bthms = map bfold [0;1;2;3] in
  let stl = `l:int32 list` in
  let wwin i = list_mk_comb(`WWIN:(int32)list->num->int128`,
                 [`m:int32 list`;mk_small_numeral(4*i)]) in
  let cryptofold =
    let th = INST ([ stl,`st:int32 list` ] @
                   (map (fun i -> kquad i, mk_var("kq"^string_of_int i,`:int128`)) [0;1;2;3]) @
                   (map (fun i -> wwin i, mk_var("b"^string_of_int i,`:int128`)) [0;1;2;3]))
              (SPEC_ALL SHA256_COMPRESS_HW_HEAD_CRYPTO_FOLD) in
    MP th (end_itlist CONJ (map REFL ((map kquad [0;1;2;3]) @ (map wwin [0;1;2;3])))) in
  let ymm3fold =
    let th = INST (map (fun i -> wwin i, mk_var("b"^string_of_int i,`:int128`)) [0;1;2;3])
              (SPEC_ALL SHA256_COMPRESS_HW_HEAD_YMM3) in
    MP th (end_itlist CONJ (map (fun i -> REFL(wwin i)) [0;1;2;3])) in
  let ymm4fold =
    let th = INST (map (fun i -> wwin i, mk_var("b"^string_of_int i,`:int128`)) [0;1;2;3])
              (SPEC_ALL SHA256_COMPRESS_HW_HEAD_YMM4) in
    MP th (end_itlist CONJ (map (fun i -> REFL(wwin i)) [0;1;2;3])) in
  let ymm5fold =
    let th = INST [wwin 2,`b2:int128`; wwin 3,`b3:int128`]
              (SPEC_ALL SHA256_COMPRESS_HW_HEAD_YMM5) in
    MP th (CONJ (REFL(wwin 2)) (REFL(wwin 3))) in
  let headB   = REWRITE_RULE bthms headI in
  let headB4  = GEN_REWRITE_RULE (RAND_CONV o TOP_DEPTH_CONV) [ymm4fold] headB in
  GEN_ALL(REWRITE_RULE [cryptofold; ymm3fold; ymm5fold] headB4);;

let ag2 nm th_bl th_orig =
  let ok = aconv (concl th_bl) (bl_of_stmt(concl th_orig)) in
  Printf.printf "GATE %-24s %s hyps=%d frees=%d\n%!" nm
    (if ok then "PASS" else "*** FAIL ***")
    (List.length(hyp th_bl)) (List.length(frees(concl th_bl)));;
ag2 "HEAD38_RAW_BL" SHA256_COMPRESS_HW_HEAD38_RAW_BL SHA256_COMPRESS_HW_HEAD38_RAW;;
ag2 "HEAD38_ABS_BL" SHA256_COMPRESS_HW_HEAD38_ABS_BL SHA256_COMPRESS_HW_HEAD38_ABS;;
Printf.printf "S062_HEAD38_DONE\n%!";;


(* ========================================================================= *)
(* Session 062 -- bl_tmc cone-port BATCH 2: the multi-block _PLUS composer     *)
(* tower (RSI/YMM7-mask/RDX-carrying loop body).  Order = dep order:            *)
(*   CORE_TAIL_TO_2F0_PLUS_BL (tail g13;g14+;g15kload, pc+0x297->0x2f0)          *)
(*   CORE_38_TO_2F0_PLUS_BL   (head-through-tail loop body, pc+0x38->0x2f0)      *)
(*   CORE_LOOP_BODY_PLUS_BL   (+ g15 crypto + feedfwd, pc+0x38->0x30c)           *)
(*   CORE_LOOP_BODY_PLUS_RIP_BL (RIP conjunct re-added for the JNE seam)         *)
(*   CORE_LOOP_BODY_SPEC_PLUS_RIP_BL (crypto fold to sha256_block, pure OCaml)   *)
(* Statements = bl_of_stmt(concl ORIGINAL); each aconv-gated (PASS).  The        *)
(* shared _PLUS OCaml scaffold is redeclared here seeded with _BL sub-lemmas +   *)
(* execup_bl; a bad swap fails the replayed ENSURES_SEQUENCE/SUBLEMMA stepping.  *)
(* ========================================================================= *)
let SHA256_COMPRESS_HW_CORE_TAIL_TO_2F0_PLUS_BL =
  let strip_atom th =
    let bod = snd(strip_forall(concl th)) in
    let ens = if is_imp bod then snd(dest_imp bod) else bod in
    let l,c = dest_comb ens in let l2,q = dest_comb l in let _,p = dest_comb l2 in (p,q,c) in
  let vbyname th n = find (fun v -> name_of v = n) (fst(strip_forall(concl th))) in
  let conjs_of_lam q = let s,body = dest_abs q in s, conjuncts body in
  let contains s sub =
    let ls=String.length s and lsub=String.length sub in
    let rec go i = i+lsub<=ls && (String.sub s i lsub = sub || go(i+1)) in go 0 in
  let is_kread off c =
    is_eq c && contains (string_of_term c) "bytes128"
            && contains (string_of_term c) ("(word " ^ off ^ ")") in
  let kread_for s src_svar src_conjs off =
    vsubst[s,src_svar] (find (is_kread off) src_conjs) in
  let ymm_rhs post nm =
    let _,cs = conjs_of_lam post in
    let hit = find (fun c -> is_eq c && contains (string_of_term(fst(dest_eq c))) nm) cs in
    snd(dest_eq hit) in
  let list_of_abef post =
    let ymm1 = ymm_rhs post "YMM1_SSE" in
    rand(rand(rator(rator(rator ymm1)))) in
  let post_ring q =
    (list_of_abef q, ymm_rhs q "YMM3_SSE", ymm_rhs q "YMM4_SSE",
     ymm_rhs q "YMM5_SSE", ymm_rhs q "YMM6_SSE") in
  let vG13 = SHA256_COMPRESS_HW_GROUP4_FULL_S_G13_BL in
  let g13th = INST [`kq0:int128`, `kq:int128`; `kq1:int128`, `kq1:int128`]
                   (SPEC_ALL vG13) in
  let (pg13,qg13,cg13) = strip_atom g13th in
  let (l13,a313,a413,a513,a613) = post_ring qg13 in
  (* g14: FULL_S_G14_PLUS (binders kq,kq1,a3..a6,mask). map kq->kq1, kq1->kq2.  *)
  let g14th =
    let base = SPEC_ALL SHA256_COMPRESS_HW_GROUP4_FULL_S_G14_PLUS_BL in
    INST [ `kq1:int128`, vbyname SHA256_COMPRESS_HW_GROUP4_FULL_S_G14_PLUS_BL "kq";
           `kq2:int128`, vbyname SHA256_COMPRESS_HW_GROUP4_FULL_S_G14_PLUS_BL "kq1";
           l13,  vbyname SHA256_COMPRESS_HW_GROUP4_FULL_S_G14_PLUS_BL "l";
           a313, vbyname SHA256_COMPRESS_HW_GROUP4_FULL_S_G14_PLUS_BL "a3";
           a413, vbyname SHA256_COMPRESS_HW_GROUP4_FULL_S_G14_PLUS_BL "a4";
           a513, vbyname SHA256_COMPRESS_HW_GROUP4_FULL_S_G14_PLUS_BL "a5";
           a613, vbyname SHA256_COMPRESS_HW_GROUP4_FULL_S_G14_PLUS_BL "a6" ] base in
  let (pg14,qg14,cg14) = strip_atom g14th in
  let (l14,a314,a414,a514,a614) = post_ring qg14 in
  let g15kth =
    let base = SPEC_ALL SHA256_COMPRESS_HW_GROUP4_G15_KLOAD_BL in
    INST [ `kq2:int128`, vbyname SHA256_COMPRESS_HW_GROUP4_G15_KLOAD_BL "kq";
           l14,  vbyname SHA256_COMPRESS_HW_GROUP4_G15_KLOAD_BL "l";
           a314, vbyname SHA256_COMPRESS_HW_GROUP4_G15_KLOAD_BL "a3";
           a414, vbyname SHA256_COMPRESS_HW_GROUP4_G15_KLOAD_BL "a4";
           a514, vbyname SHA256_COMPRESS_HW_GROUP4_G15_KLOAD_BL "a5";
           a614, vbyname SHA256_COMPRESS_HW_GROUP4_G15_KLOAD_BL "a6" ] base in
  let (pg15,qg15,cg15) = strip_atom g15kth in
  let svar13,pg13c = conjs_of_lam pg13 in
  let sg14,pg14c = conjs_of_lam pg14 in
  let sg15,pg15c = conjs_of_lam pg15 in
  let sv = `s:x86state` in
  let rdx_rider = `read RDX s = (rdxin:int64)` in
  let mask_rider = `word_subword (read YMM8_SSE s) (0,128) = (mask:int128)` in
  let ymm7_post = `word_subword (read YMM7_SSE s) (0,128) = (mask:int128)` in
  let mk_r r s = vsubst[s,sv] r in
  (* frame: same as CORE_TAIL_TO_2F0 (YMM7 in MAYCHANGE, it IS written by g14). *)
  let full_frame =
    `MAYCHANGE [RIP] ,,
     MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM5_SSE; YMM6_SSE; YMM7_SSE] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]` in
  (* PRE = g13 pre-core + K@352 (rides to g14/g15) + RDX + YMM8=mask riders.    *)
  let pre_extra = [ kread_for svar13 sg14 pg14c "352" ] in
  let pre_lam = mk_abs(svar13,
    list_mk_conj (pg13c @ pre_extra @ [mk_r rdx_rider svar13; mk_r mask_rider svar13])) in
  (* POST = g15kload post-core + RDX + YMM7=mask + YMM8=mask.                    *)
  let sg15q,qg15c = conjs_of_lam qg15 in
  let post_lam = mk_abs(sg15q,
    list_mk_conj (qg15c @ [mk_r rdx_rider sg15q; mk_r ymm7_post sg15q; mk_r mask_rider sg15q])) in
  let ens_head = rator(rator(rator(snd(dest_imp(snd(strip_forall(concl vG13))))))) in
  let mk_ensures p q c = mk_comb(mk_comb(mk_comb(ens_head,p),q),c) in
  let bvars = [`pc:num`;`kbase:num`;`kptr:int64`;`l:int32 list`;
               `kq0:int128`;`kq1:int128`;`kq2:int128`;
               `a3:int128`;`a4:int128`;`a5:int128`;`a6:int128`;`rdxin:int64`;`mask:int128`] in
  let hyps = list_mk_conj
    [`aligned 16 (word_add (kptr:int64) (word 288))`;
     `aligned 16 (word_add (kptr:int64) (word 320))`;
     `aligned 16 (word_add (kptr:int64) (word 352))`] in
  let comp_concl = list_mk_forall(bvars, mk_imp(hyps, mk_ensures pre_lam post_lam full_frame)) in
  let seam_core pre =
    let s,cs = conjs_of_lam pre in
    let keep c = not(contains (string_of_term c) "bytes_loaded")
                 && not(contains (string_of_term c) "read RIP") in
    (s, filter keep cs) in
  (* seamQ1 @0x2c2 = g14_PLUS pre-core + RDX + (YMM8=mask already in g14 pre).   *)
  let seamQ1 = let s,cs = seam_core pg14 in mk_abs(s, list_mk_conj (cs @ [mk_r rdx_rider s])) in
  (* seamQ2 @0x2e4 = g15kload pre-core + RDX + YMM7=mask + YMM8=mask riders.     *)
  let seamQ2 = let s,cs = seam_core pg15 in
    mk_abs(s, list_mk_conj (cs @ [mk_r rdx_rider s; mk_r ymm7_post s; mk_r mask_rider s])) in
  prove
   (bl_of_stmt (concl SHA256_COMPRESS_HW_CORE_TAIL_TO_2F0_PLUS),
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[SOME_FLAGS] THEN
    ENSURES_SEQUENCE_TAC `pc + 0x2c2` seamQ1 THEN CONJ_TAC THENL
     [MP_TAC(REWRITE_RULE[SOME_FLAGS] g13th) THEN ASM_REWRITE_TAC[] THEN
      ENSURES_SUBLEMMA_TAC execup_bl "s" "s'" THEN ASM_REWRITE_TAC[];
      ENSURES_SEQUENCE_TAC `pc + 0x2e4` seamQ2 THEN CONJ_TAC THENL
       [MP_TAC(REWRITE_RULE[SOME_FLAGS] g14th) THEN ASM_REWRITE_TAC[] THEN
        (ENSURES_SUBLEMMA_TAC execup_bl "s" "s'" ORELSE
         ENSURES_SUBLEMMA_REFL_TAC execup_bl "s" "s'") THEN ASM_REWRITE_TAC[];
        MP_TAC(REWRITE_RULE[SOME_FLAGS] g15kth) THEN ASM_REWRITE_TAC[] THEN
        (ENSURES_SUBLEMMA_TAC execup_bl "s" "s'" ORELSE
         ENSURES_SUBLEMMA_REFL_TAC execup_bl "s" "s'") THEN ASM_REWRITE_TAC[]]]);;
Printf.printf "S053_CORE_TAIL_TO_2F0_PLUS hyps=%d frees=%d\n%!"
  (List.length (hyp SHA256_COMPRESS_HW_CORE_TAIL_TO_2F0_PLUS_BL))
  (List.length (frees (concl SHA256_COMPRESS_HW_CORE_TAIL_TO_2F0_PLUS_BL)));;
Printf.printf "S053_CORETAILPLUS_DONE\n%!";;
let agc nm th_bl th_orig =
  let ok = aconv (concl th_bl) (bl_of_stmt(concl th_orig)) in
  Printf.printf "GATE %-28s %s hyps=%d frees=%d\n%!" nm
    (if ok then "PASS" else "*** FAIL ***")
    (List.length(hyp th_bl)) (List.length(frees(concl th_bl)));;
agc "CORE_TAIL_TO_2F0_PLUS_BL" SHA256_COMPRESS_HW_CORE_TAIL_TO_2F0_PLUS_BL SHA256_COMPRESS_HW_CORE_TAIL_TO_2F0_PLUS;;
Printf.printf "S062_CTT2F0PLUS_DONE\n%!";;

(* --- generic helpers (re-declared locally to be safe) --- *)
let sv = `s:x86state`;;
let contains s sub =
  let ls=String.length s and lsub=String.length sub in
  let rec go i = i+lsub<=ls && (String.sub s i lsub = sub || go(i+1)) in go 0;;
let strip_atom th =
  let bod = snd(strip_forall(concl th)) in
  let ens = if is_imp bod then snd(dest_imp bod) else bod in
  let l,c = dest_comb ens in let l2,q = dest_comb l in let _,p = dest_comb l2 in (p,q,c);;
let ens_of th = let bod = snd(strip_forall(concl th)) in
  if is_imp bod then snd(dest_imp bod) else bod;;
let conjs_of_lam q = let s,body = dest_abs q in s, conjuncts body;;
let findc sub cs = find (fun c -> contains (string_of_term c) sub) cs;;
let rebase lam = let s,cs = conjs_of_lam lam in map (vsubst[sv,s]) cs;;
let keepseam c = not(contains (string_of_term c) "bytes_loaded")
                 && not(contains (string_of_term c) "read RIP");;
let core cs = filter keepseam cs;;
let is_kread off c =
  is_eq c && contains (string_of_term c) "bytes128"
          && contains (string_of_term c) ("(word " ^ off ^ ")");;
let kread_in off cs = find (is_kread off) cs;;
let nred_rule = CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV
                          THENC DEPTH_CONV NUM_SUB_CONV THENC DEPTH_CONV NUM_LE_CONV);;
let pcterm n = mk_comb(mk_comb(`(+):num->num->num`,`pc:num`), mk_small_numeral n);;
let masklit = `word 16018520953223639909183530438118932995 : int128`;;

(* --- rebuild CORE_38_TO_2F0 pieces with RSI as an extra rider --- *)
let stlist = `l:int32 list`;;
let kquad n =
  let el j = list_mk_comb(`EL:num->(int32)list->int32`,
               [mk_small_numeral(4*n+j);`sha256_constants:int32 list`]) in
  list_mk_comb(`WQUAD:int32->int32->int32->int32->int128`,[el 0;el 1;el 2;el 3]);;
let steady_leg th g =
  let sp = SPECL [`pc:num`;`kbase:num`;`kptr:int64`;`m:int32 list`;stlist;
                  mk_small_numeral g] th in
  REWRITE_RULE[] (nred_rule (SPEC (kquad (g+1)) sp));;
let head = INST [kquad 4, `kq4:int128`] (SPEC_ALL SHA256_COMPRESS_HW_HEAD38_ABS_BL);;
let steadies =
 [ (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_R0_BL  4),  4, 0x0f4, 0x120;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_R1_BL  5),  5, 0x120, 0x14d;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_R2_BL  6),  6, 0x14d, 0x17a;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_R3_BL  7),  7, 0x17a, 0x1a7;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_G8_BL  8),  8, 0x1a7, 0x1d7;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_G9_BL  9),  9, 0x1d7, 0x207;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_G10_BL 10), 10, 0x207, 0x237;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_G11_BL 11), 11, 0x237, 0x267;
   (steady_leg SHA256_COMPRESS_HW_SPEC_STEP_G12_BL 12), 12, 0x267, 0x297 ];;
let stlist_cr52 = `sha256_compress_rounds m (l:int32 list) 52 : int32 list`;;
let tail = SPECL [`pc:num`;`kbase:num`;`kptr:int64`; stlist_cr52;
                  kquad 13; `kqA:int128`; `kqB:int128`;
                  `WWIN m 48:int128`;`WWIN m 52:int128`;
                  `PADP m 40:int128`;`MSG1P m 44:int128`;`rdxin:int64`; masklit]
             SHA256_COMPRESS_HW_CORE_TAIL_TO_2F0_PLUS_BL;;
let (pH,qH,fH) = strip_atom head;;
let pHc = rebase pH and qHc = rebase qH;;
let ymm9  = findc "YMM9_SSE" qHc;;
let ymm10 = findc "YMM10_SSE" qHc;;
let rsi_rider = `read RSI s = word_add mptr (word 64)`;;   (* NEW rider *)
let rdx_rider0 = `read RDX s = (rdxin:int64)`;;
let ymm8_rider = `word_subword (read YMM8_SSE s) (0,128) =
                  word 16018520953223639909183530438118932995 : int128`;;
let riders = [ymm9; ymm10; rdx_rider0; ymm8_rider; rsi_rider];;  (* + RSI *)
let leg_pre th = rebase (let (p,_,_)=strip_atom th in p);;
let leg_th (th,_,_,_) = th;;
let steady_offs = [32;64;96;128;160;192;224;256;288];;
let tail_offs   = [320;352];;
let allwin = steady_offs @ tail_offs;;
let steady_kterm off =
  let k = off/32 in let leg = List.nth steadies (k-1) in
  kread_in (string_of_int off) (leg_pre (leg_th leg));;
let pTc = rebase (let (p,_,_)=strip_atom tail in p);;
let kterm off =
  if off <= 288 then steady_kterm off else kread_in (string_of_int off) pTc;;
let no_riders cs = filter (fun c -> not(contains (string_of_term c) "read RDX")
                       && not(contains (string_of_term c) "YMM8_SSE")
                       && not(contains (string_of_term c) "read RSI")) cs;;
let seam_steady (th,g,_,_) =
  let c = 32*(g-4) in
  let carry = map kterm (filter (fun w -> not(w <= c+32)) allwin) in
  mk_abs(sv, list_mk_conj (core (leg_pre th) @ riders @ carry));;
let seam_tail =
  mk_abs(sv, list_mk_conj (no_riders (core pTc) @ riders));;
let (_,qTail,_) = strip_atom tail;;
let qTailc = rebase qTail;;
let post_lam = mk_abs(sv, list_mk_conj (no_riders qTailc @ riders));;
let pre_lam = mk_abs(sv, list_mk_conj (pHc @ map kterm allwin @ [rdx_rider0; ymm8_rider]));;
let ens_head = rator(rator(rator(ens_of head)));;
let mk_ensures p q c = mk_comb(mk_comb(mk_comb(ens_head,p),q),c);;
let comp_frame =
  `MAYCHANGE [RIP; RSI] ,,
   MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM5_SSE;
              YMM6_SSE; YMM7_SSE; YMM9_SSE; YMM10_SSE] ,,
   MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;
let bvars = [`pc:num`;`kbase:num`;`kptr:int64`;`m:int32 list`;`l:int32 list`;
             `mptr:int64`;`kqA:int128`;`kqB:int128`;`rdxin:int64`];;
let comp_hyps = list_mk_conj
 [`aligned 16 (kptr:int64)`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551488))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551520))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551552))`;
  `aligned 16 (word_add (kptr:int64) (word 18446744073709551584))`];;
let comp_concl = list_mk_forall(bvars, mk_imp(comp_hyps, mk_ensures pre_lam post_lam comp_frame));;
Printf.printf "CORE_38_TO_2F0_PLUS concl built. frees(concl)=%d\n%!" (List.length(frees comp_concl));;

(* execup_bl is already bound by the loaded file (line 2302); reuse it. *)
let leg_tac th =
  MP_TAC(REWRITE_RULE[SOME_FLAGS] th) THEN ASM_REWRITE_TAC[] THEN
  (ENSURES_SUBLEMMA_TAC execup_bl "s" "s'" ORELSE
   ENSURES_SUBLEMMA_REFL_TAC execup_bl "s" "s'") THEN ASM_REWRITE_TAC[];;
let rec build entries final = match entries with
  | [] -> leg_tac final
  | (off,seam,disch)::rest ->
      ENSURES_SEQUENCE_TAC (pcterm off) seam THEN
      CONJ_TAC THENL [ leg_tac disch; build rest final ];;
let steady_entries =
  let rec go prev = function
    | [] -> []
    | (th,g,e,x)::rest -> (e, seam_steady (th,g,e,x), prev) :: go th rest in
  match steadies with
  | (th0,g0,e0,x0)::rest -> (e0, seam_steady (th0,g0,e0,x0), head) :: go th0 rest
  | [] -> failwith "no steadies";;
let g12th = leg_th (List.nth steadies 8);;
let entries = steady_entries @ [ 0x297, seam_tail, g12th ];;
let mk_align_term n =
  vsubst [mk_small_numeral n, `n:num`]
    `aligned 16 (word_add (kptr:int64) (word n))`;;
let mk_align_sub n =
  let t = mk_align_term n in
  SUBGOAL_THEN t ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORMALIZE_ALIGNED_WORD_CONV t]; ALL_TAC];;

let SHA256_COMPRESS_HW_CORE_38_TO_2F0_PLUS_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_CORE_38_TO_2F0_PLUS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  EVERY (map mk_align_sub [32;64;96;128;160;192;224;256;288;320;352]) THEN
  build entries tail);;
Printf.printf "S054_CORE_38_TO_2F0_PLUS hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_CORE_38_TO_2F0_PLUS_BL))
  (List.length(frees(concl SHA256_COMPRESS_HW_CORE_38_TO_2F0_PLUS_BL)));;
Printf.printf "S054_CORE_38_TO_2F0_PLUS_DONE\n%!";;
let agc nm th_bl th_orig =
  let ok = aconv (concl th_bl) (bl_of_stmt(concl th_orig)) in
  Printf.printf "GATE %-28s %s hyps=%d frees=%d\n%!" nm
    (if ok then "PASS" else "*** FAIL ***")
    (List.length(hyp th_bl)) (List.length(frees(concl th_bl)));;
agc "CORE_38_TO_2F0_PLUS_BL" SHA256_COMPRESS_HW_CORE_38_TO_2F0_PLUS_BL SHA256_COMPRESS_HW_CORE_38_TO_2F0_PLUS;;
Printf.printf "S062_C38PLUS_DONE\n%!";;

(* ========================================================================= *)
(* CORE_LOOP_BODY_PLUS: compose CORE_38_TO_2F0_PLUS ; G15_RAW_PLUS ;          *)
(* FEEDFWD_PLUS, threading RSI (rides G15/FF frames) and YMM7=mask (rides too) *)
(* into the final POST.  Mirrors the s053 CORE_LOOP_BODY block but with the    *)
(* PLUS core38 and RSI/YMM7 added to seams+post.                               *)
(* ========================================================================= *)
let ymm_rhs cs nm = snd(dest_eq(findc nm cs));;
let core38 = SPEC_ALL SHA256_COMPRESS_HW_CORE_38_TO_2F0_PLUS_BL;;
let (pc0,qc0,fc0) = strip_atom core38;;
let qc0c = rebase qc0;;
let wk_t   = ymm_rhs qc0c "YMM0_SSE";;
let abef_t = ymm_rhs qc0c "YMM1_SSE";;
let cdgh_t = ymm_rhs qc0c "YMM2_SSE";;
let a3_t   = ymm_rhs qc0c "YMM3_SSE";;
let a4_t   = ymm_rhs qc0c "YMM4_SSE";;
let a5_t   = ymm_rhs qc0c "YMM5_SSE";;
let a6_t   = ymm_rhs qc0c "YMM6_SSE";;
let ia_t   = ymm_rhs qc0c "YMM9_SSE";;
let ic_t   = ymm_rhs qc0c "YMM10_SSE";;
let kq352_t = snd(dest_eq(find (fun c -> contains (string_of_term c) "(word 352)")
                            (filter is_eq qc0c)));;
let g15p = SPECL [`pc:num`;`kbase:num`;`kptr:int64`;
                  `word_add kptr (word 352):int64`; kq352_t;
                  wk_t; abef_t; cdgh_t; a3_t; a4_t; a5_t; a6_t; `rdxin:int64`]
             SHA256_COMPRESS_HW_GROUP_STEP4_G15_RAW_PLUS_BL;;
let (pg,qg,fg) = strip_atom g15p;;
let qgc = rebase qg;;
let g15_abef = ymm_rhs qgc "YMM1_SSE";;
let g15_cdgh = ymm_rhs qgc "YMM2_SSE";;
let ffp = SPECL [`pc:num`;`kbase:num`; g15_abef; g15_cdgh; ia_t; ic_t;
                 `word_sub rdxin (word 1):int64`;
                 `val (word_sub rdxin (word 1):int64) = 0`]
            SHA256_COMPRESS_HW_FEEDFWD_PLUS_BL;;
let (pf,qf,ff) = strip_atom ffp;;
let qfc = rebase qf;;

let pre_lam = pc0;;
(* POST = FEEDFWD post-core + RSI=mptr+64 + YMM7=mask (both ride G15/FF). *)
let rsi_post = `read RSI s = word_add mptr (word 64)`;;
let mask7 = `word_subword (read YMM7_SSE s) (0,128) =
             word 16018520953223639909183530438118932995 : int128`;;
let mask8 = `word_subword (read YMM8_SSE s) (0,128) =
             word 16018520953223639909183530438118932995 : int128`;;
let post_lam = mk_abs(sv, list_mk_conj (core qfc @ [rsi_post; mask7; mask8]));;

let ens_head2 = rator(rator(rator(ens_of core38)));;
let mk_ensures2 p q c = mk_comb(mk_comb(mk_comb(ens_head2,p),q),c);;
let comp_frame2 =
  `MAYCHANGE [RIP; RSI; RDX] ,,
   MAYCHANGE [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE; YMM4_SSE; YMM5_SSE;
              YMM6_SSE; YMM7_SSE; YMM9_SSE; YMM10_SSE] ,,
   MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;
let comp_concl2 = list_mk_forall(bvars, mk_imp(comp_hyps, mk_ensures2 pre_lam post_lam comp_frame2));;
Printf.printf "CORE_LOOP_BODY_PLUS concl built. frees=%d\n%!" (List.length(frees comp_concl2));;

(* seamA @0x2f0 = G15 PRE-core + mask(7/8) + init(9/10) + RSI riders.          *)
let ymm9_r  = subst [ia_t,`initabef0:int128`]
   `word_subword (read YMM9_SSE s) (0,128) = (initabef0:int128)`;;
let ymm10_r = subst [ic_t,`initcdgh0:int128`]
   `word_subword (read YMM10_SSE s) (0,128) = (initcdgh0:int128)`;;
let seamA = mk_abs(sv, list_mk_conj (core (rebase pg) @ [mask7; mask8; ymm9_r; ymm10_r; rsi_post]));;
let seamB = mk_abs(sv, list_mk_conj (core (rebase pf) @ [mask7; mask8; rsi_post]));;

let SHA256_COMPRESS_HW_CORE_LOOP_BODY_PLUS_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_CORE_LOOP_BODY_PLUS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC (pcterm 0x2f0) seamA THEN CONJ_TAC THENL
   [leg_tac core38;
    ENSURES_SEQUENCE_TAC (pcterm 0x302) seamB THEN CONJ_TAC THENL
     [leg_tac g15p;
      leg_tac ffp]]);;
Printf.printf "S054_CORE_LOOP_BODY_PLUS hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_CORE_LOOP_BODY_PLUS_BL))
  (List.length(frees(concl SHA256_COMPRESS_HW_CORE_LOOP_BODY_PLUS_BL)));;
Printf.printf "S054_CORE_LOOP_BODY_PLUS_DONE\n%!";;
let agc nm th_bl th_orig =
  let ok = aconv (concl th_bl) (bl_of_stmt(concl th_orig)) in
  Printf.printf "GATE %-28s %s hyps=%d frees=%d\n%!" nm
    (if ok then "PASS" else "*** FAIL ***")
    (List.length(hyp th_bl)) (List.length(frees(concl th_bl)));;
agc "CORE_LOOP_BODY_PLUS_BL" SHA256_COMPRESS_HW_CORE_LOOP_BODY_PLUS_BL SHA256_COMPRESS_HW_CORE_LOOP_BODY_PLUS;;
Printf.printf "S062_CLBPLUS_DONE\n%!";;

(* ===== s062 bl-port: CORE_LOOP_BODY_PLUS_RIP_BL ===== *)
(* RIP conjunct at the FEEDFWD exit (pc+0x30c = pc+780). *)
let rip_post = `read RIP s = word (pc + 0x30c)`;;
let post_lam_rip =
  let v, body = dest_abs post_lam in
  mk_abs(v, list_mk_conj (rip_post :: conjuncts body));;
let comp_concl2_rip =
  list_mk_forall(bvars, mk_imp(comp_hyps, mk_ensures2 pre_lam post_lam_rip comp_frame2));;

let SHA256_COMPRESS_HW_CORE_LOOP_BODY_PLUS_RIP_BL = prove
 (bl_of_stmt (concl SHA256_COMPRESS_HW_CORE_LOOP_BODY_PLUS_RIP),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC (pcterm 0x2f0) seamA THEN CONJ_TAC THENL
   [leg_tac core38;
    ENSURES_SEQUENCE_TAC (pcterm 0x302) seamB THEN CONJ_TAC THENL
     [leg_tac g15p;
      leg_tac ffp]]);;
Printf.printf "S055_CLB_PLUS_RIP hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_CORE_LOOP_BODY_PLUS_RIP_BL))
  (List.length(frees(concl SHA256_COMPRESS_HW_CORE_LOOP_BODY_PLUS_RIP_BL)));;

(* ===== s062 bl-port: CORE_LOOP_BODY_SPEC_PLUS_RIP_BL (pure fold) ===== *)
(* CLB_SPEC_PLUS_RIP: the CLB_SPEC_PLUS crypto fold applied to CLB_PLUS_RIP.    *)
(* Identical recipe (lines 8700-8736); the RIP conjunct is inert under it.      *)
let SHA256_COMPRESS_HW_CORE_LOOP_BODY_SPEC_PLUS_RIP_BL =
  let kqA_val = `WQUAD (EL 56 sha256_constants) (EL 57 sha256_constants)
                       (EL 58 sha256_constants) (EL 59 sha256_constants) : int128` in
  let kqB_val = `WQUAD (EL 60 sha256_constants) (EL 61 sha256_constants)
                       (EL 62 sha256_constants) (EL 63 sha256_constants) : int128` in
  let body' = INST [kqA_val, `kqA:int128`; kqB_val, `kqB:int128`]
                (SPEC_ALL SHA256_COMPRESS_HW_CORE_LOOP_BODY_PLUS_RIP_BL) in
  let nred_cr  = CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV) in
  let nred_off = CONV_RULE(DEPTH_CONV NUM_ADD_CONV) in
  let cr_step g = nred_cr (SPECL [`m:int32 list`; `l:int32 list`; mk_small_numeral g]
                            CR4_SPEC_STEP_WWIN) in
  let cr52 = cr_step 13 and cr56 = cr_step 14 and cr60 = cr_step 15 in
  let wring40 = nred_off (SPECL [`m:int32 list`; `40`] WRING_WWIN) in
  let wring44 = nred_off (SPECL [`m:int32 list`; `44`] WRING_WWIN) in
  let padp44  = GSYM(nred_off (SPECL [`m:int32 list`; `44`] PADP)) in
  let stepA = REWRITE_RULE[wring40; padp44; wring44; cr52; cr56] body' in
  let l60 = `sha256_compress_rounds m (l:int32 list) 60 : int32 list` in
  let wk15 = `simd4 word_add
     (WQUAD (EL 60 sha256_constants) (EL 61 sha256_constants)
            (EL 62 sha256_constants) (EL 63 sha256_constants))
     (WWIN m 60) : int128` in
  let GA = CONV_RULE(TOP_DEPTH_CONV let_CONV)
             (SPECL [l60; wk15] SHA256_RNDS2_GROUP_ADVANCE) in
  let GA1 = CONJUNCT1 GA and GA2 = CONJUNCT2 GA in
  let ATCF = CONV_RULE(TOP_DEPTH_CONV let_CONV)
    (ISPECL [l60;
             `word_subword (wk15v:int128) (0,32):int32`; `word_subword (wk15v:int128) (32,32):int32`;
             `word_subword (wk15v:int128) (64,32):int32`; `word_subword (wk15v:int128) (96,32):int32`]
            ABEF_TWO_IS_CDGH_FOUR) in
  let ATCF = INST [wk15, `wk15v:int128`] ATCF in
  let stepB0 = REWRITE_RULE[GA1] stepA in
  let stepB1 = REWRITE_RULE[GA2] stepB0 in
  let stepB  = REWRITE_RULE[ATCF] stepB1 in
  let stepC = REWRITE_RULE[cr60] (REWRITE_RULE[GSYM CR4] stepB) in
  let step2 = REWRITE_RULE[SIMD4_ADD_ABEF; SIMD4_ADD_CDGH] stepC in
  let step3 = REWRITE_RULE[GSYM BLOCK_ELS_L] step2 in
  GEN_ALL step3;;
Printf.printf "S055_CLB_SPEC_PLUS_RIP hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_CORE_LOOP_BODY_SPEC_PLUS_RIP_BL))
  (List.length(frees(concl SHA256_COMPRESS_HW_CORE_LOOP_BODY_SPEC_PLUS_RIP_BL)));;

let agc nm th_bl th_orig =
  let ok = aconv (concl th_bl) (bl_of_stmt(concl th_orig)) in
  Printf.printf "GATE %-32s %s hyps=%d frees=%d\n%!" nm
    (if ok then "PASS" else "*** FAIL ***")
    (List.length(hyp th_bl)) (List.length(frees(concl th_bl)));;
agc "CORE_LOOP_BODY_PLUS_RIP_BL" SHA256_COMPRESS_HW_CORE_LOOP_BODY_PLUS_RIP_BL SHA256_COMPRESS_HW_CORE_LOOP_BODY_PLUS_RIP;;
agc "CORE_LOOP_BODY_SPEC_PLUS_RIP_BL" SHA256_COMPRESS_HW_CORE_LOOP_BODY_SPEC_PLUS_RIP_BL SHA256_COMPRESS_HW_CORE_LOOP_BODY_SPEC_PLUS_RIP;;
Printf.printf "S062_RIPTOWER_DONE\n%!";;


(* ========================================================================= *)
(* Session 062 -- bl_tmc cone-port BATCH 3: CORE_LOOP_STEP_RAW_BL +           *)
(* CORE_CORRECT_BL (the milestone: the whole multi-block SysV core over        *)
(* bl_tmc).  CORE_LOOP_STEP_RAW_BL = CLB_SPEC_PLUS_RIP_BL ; JNE_BR_BL (one      *)
(* loop iteration + abstract-ZF back-edge).  CORE_CORRECT_BL statement =        *)
(* bl_of_stmt_reg(concl CORE_CORRECT) (825->820 region numeral; the unrelated   *)
(* 820 K-offset left alone), proved by the verbatim UP2 tactic w/ _BL sub-refs  *)
(* (ENTRY_REPACK_BL/CORE_LOOP_STEP_RAW_BL/EXIT_BL) + execup_bl.  loopinv_tm      *)
(* carries no code image (bl_of_stmt-identical), so it is reused unchanged.      *)
(* aconv-gated PASS, hyps=0 frees=0.                                            *)
(* ========================================================================= *)
let SHA256_COMPRESS_HW_CORE_LOOP_STEP_RAW_BL =
  let clb = SPEC_ALL SHA256_COMPRESS_HW_CORE_LOOP_BODY_SPEC_PLUS_RIP_BL in
  let clb_body = snd(strip_forall(concl clb)) in
  let clb_ant, clb_ens = dest_imp clb_body in
  let clb_pre  = rand(rator(rator clb_ens)) in
  let clb_post = rand(rator clb_ens) in
  let clb_frame = rand clb_ens in
  let clb_post_conjs = conjuncts(snd(dest_abs clb_post)) in
  (* c is `read RIP s = ...` iff its LHS is `read RIP s` (rator = `read RIP`,   *)
  (* itself `read` applied to the component `RIP`).  string_of_term match is     *)
  (* robust to the read/RIP being combs (dest_const on `read RIP` throws).       *)
  let is_rip c =
    (try string_of_term(rand(rator(lhs c))) = "RIP" with _ -> false) in
  let non_rip = filter (fun c -> not(is_rip c)) clb_post_conjs in
  let jne_rip = `read RIP s =
     (if (val (word_sub (rdxin:int64) (word 1)) = 0)
      then word (pc + 0x312) else word (pc + 0x38))` in
  let step_post = mk_abs(`s:x86state`, list_mk_conj (jne_rip :: non_rip)) in
  let ens_head = rator(rator(rator clb_ens)) in
  let step_ens = mk_comb(mk_comb(mk_comb(ens_head, clb_pre), step_post), clb_frame) in
  let step_bvars = [`kbase:num`;`pc:num`;`kptr:int64`;`rdxin:int64`;
                    `m:int32 list`;`l:int32 list`;`mptr:int64`] in
  let step_concl = list_mk_forall(step_bvars, mk_imp(clb_ant, step_ens)) in
  (* seam @pc+0x30c = clb_post MINUS its RIP conjunct (ENSURES_SEQUENCE_TAC        *)
  (* auto-injects read RIP s = word pc'; leaving it in the seam duplicates RIP and *)
  (* leaves the spurious residual `(if ... then pc+786 else pc+56) = word(pc+780)`).*)
  let seam = mk_abs(`s:x86state`,
               list_mk_conj (filter (fun c -> not(is_rip c))
                              (conjuncts(snd(dest_abs clb_post))))) in
  let jne_inst = SPECL [`pc:num`;`kbase:num`;
                        `val (word_sub (rdxin:int64) (word 1)) = 0`]
                   SHA256_COMPRESS_HW_JNE_BR_BL in
  prove
   (bl_of_stmt (concl SHA256_COMPRESS_HW_CORE_LOOP_STEP_RAW),
    REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
    ENSURES_SEQUENCE_TAC `pc + 0x30c` seam THEN CONJ_TAC THENL
     [MP_TAC(REWRITE_RULE[SOME_FLAGS] clb) THEN ASM_REWRITE_TAC[] THEN
      (ENSURES_SUBLEMMA_TAC execup_bl "s" "s'" ORELSE
       ENSURES_SUBLEMMA_REFL_TAC execup_bl "s" "s'") THEN ASM_REWRITE_TAC[];
      MP_TAC jne_inst THEN ASM_REWRITE_TAC[] THEN
      (ENSURES_SUBLEMMA_TAC execup_bl "s" "s'" ORELSE
       ENSURES_SUBLEMMA_REFL_TAC execup_bl "s" "s'") THEN ASM_REWRITE_TAC[]]);;
Printf.printf "S055_CORE_LOOP_STEP_RAW hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_CORE_LOOP_STEP_RAW_BL))
  (List.length(frees(concl SHA256_COMPRESS_HW_CORE_LOOP_STEP_RAW_BL)));;
let agc nm th_bl th_orig =
  let ok = aconv (concl th_bl) (bl_of_stmt(concl th_orig)) in
  Printf.printf "GATE %-28s %s hyps=%d frees=%d\n%!" nm
    (if ok then "PASS" else "*** FAIL ***")
    (List.length(hyp th_bl)) (List.length(frees(concl th_bl)));;
agc "CORE_LOOP_STEP_RAW_BL" SHA256_COMPRESS_HW_CORE_LOOP_STEP_RAW_BL SHA256_COMPRESS_HW_CORE_LOOP_STEP_RAW;;
Printf.printf "S062_STEPRAW_DONE\n%!";;

let SHA256_COMPRESS_HW_CORE_CORRECT_BL = prove
 (bl_of_stmt_reg (concl SHA256_COMPRESS_HW_CORE_CORRECT),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  SUBGOAL_THEN `~(num_blocks = 0)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ENSURES_WHILE_UP2_TAC `num_blocks:num` `pc + 0x38` `pc + 0x312` loopinv_tm THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ (* ENTRY leg: ENTRY_REPACK (sptr as its dptr, q0/q1 = the H WQUADs) *)
     MP_TAC(ISPECL
       [`pc:num`;`kbase:num`;`kptr:int64`;`sptr:int64`;
        `WQUAD (EL 0 H) (EL 1 H) (EL 2 H) (EL 3 H):int128`;
        `WQUAD (EL 4 H) (EL 5 H) (EL 6 H) (EL 7 H):int128`;
        `word 16018520953223639909183530438118932995:int128`]
       SHA256_COMPRESS_HW_ENTRY_REPACK_BL) THEN
     ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[sha256_hash_blocks; SUB_0; MULT_CLAUSES; WORD_ADD_0;
                 WQUAD_SUBWORD] THEN
     ENSURES_SUBLEMMA_TAC execup_bl "s" "s'" THEN
     ASM_REWRITE_TAC[WQUAD_SUBWORD];
     (* BODY leg (pc+0x38 loopinv i -> (if i+1<nb then pc+0x38 else pc+0x312)    *)
     (* loopinv(i+1)).  s055: discharged.  Compose CORE_LOOP_STEP_RAW (= one     *)
     (* loop iteration CLB_SPEC_PLUS_RIP ; JNE_BR) instantiated at l:=            *)
     (* hash_blocks m H i, block i, ptr dptr+64i, count word(nb-i), lift via the *)
     (* SUBLEMMA, reconcile:                                                     *)
     (*   pre  (loopinv i => STEP_PRE): specialize the quantified message        *)
     (*        conjunct at j:=i (ASM_SIMP) + normalize addresses (MSG_ADDR).      *)
     (*   post (STEP_POST => loopinv(i+1)): HB_STEP folds block(m i)(hb i)->      *)
     (*        hb(i+1); RSI_STEP/RDX_STEP the pointer/counter; RIP_COND the       *)
     (*        ZF-driven back-edge target.  RDI/K/message ride the frame.         *)
     REPEAT STRIP_TAC THEN
     SUBGOAL_THEN `num_blocks < 2 EXP 64` ASSUME_TAC THENL
      [TRANS_TAC LET_TRANS `val (dptr:int64) + 64 * num_blocks` THEN
       ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
     MP_TAC(REWRITE_RULE[SOME_FLAGS]
       (SPECL [`kbase:num`;`pc:num`;`kptr:int64`;`word (num_blocks - i):int64`;
               `(m:num->int32 list) i`; `sha256_hash_blocks m H i`;
               `word_add dptr (word (64 * i)):int64`]
          SHA256_COMPRESS_HW_CORE_LOOP_STEP_RAW_BL)) THEN
     ASM_REWRITE_TAC[] THEN
     (ENSURES_SUBLEMMA_TAC execup_bl "s" "s'" ORELSE
      ENSURES_SUBLEMMA_REFL_TAC execup_bl "s" "s'") THENL
      [ ASM_SIMP_TAC[MSG_ADDR];
        REWRITE_TAC[SHA256_HW_HB_STEP] THEN
        ASM_SIMP_TAC[SHA256_HW_RSI_STEP; SHA256_HW_RDX_STEP; RIP_COND] ];
     (* EXIT leg (pc+0x312 loopinv num_blocks -> pc+0x334, EXIT + store).       *)
     (* s055: discharged.  Mirror the proven single-block CORE_BODY leg_tac      *)
     (* (line ~7518): instantiate EXIT with abef/cdgh := the hash_blocks packs,  *)
     (* MP_TAC with SOME_FLAGS expanded so ASM_REWRITE discharges EXIT's          *)
     (* nonoverlapping antecedent (the s054 No-match was an undischarged          *)
     (* antecedent + missing REFL fallback, not the math), then the SUBLEMMA      *)
     (* lift (ORELSE reflexive), then close the stored WQUADs via                 *)
     (* ABEF/CDGH_PACK_SUBWORDS.                                                  *)
     MP_TAC(REWRITE_RULE[SOME_FLAGS]
       (SPECL [`pc:num`;`kbase:num`;`sptr:int64`;
          `ABEF_PACK (EL 0 (sha256_hash_blocks m H num_blocks))
                     (EL 1 (sha256_hash_blocks m H num_blocks))
                     (EL 4 (sha256_hash_blocks m H num_blocks))
                     (EL 5 (sha256_hash_blocks m H num_blocks)):int128`;
          `CDGH_PACK (EL 2 (sha256_hash_blocks m H num_blocks))
                     (EL 3 (sha256_hash_blocks m H num_blocks))
                     (EL 6 (sha256_hash_blocks m H num_blocks))
                     (EL 7 (sha256_hash_blocks m H num_blocks)):int128`]
          SHA256_COMPRESS_HW_EXIT_BL)) THEN
     ASM_REWRITE_TAC[] THEN
     (ENSURES_SUBLEMMA_TAC execup_bl "s" "s'" ORELSE
      ENSURES_SUBLEMMA_REFL_TAC execup_bl "s" "s'") THEN
     ASM_REWRITE_TAC[ABEF_PACK_SUBWORDS; CDGH_PACK_SUBWORDS] ]);;
let agc nm th_bl th_orig =
  let ok = aconv (concl th_bl) (bl_of_stmt_reg(concl th_orig)) in
  Printf.printf "GATE %-24s %s hyps=%d frees=%d\n%!" nm
    (if ok then "PASS" else "*** FAIL ***")
    (List.length(hyp th_bl)) (List.length(frees(concl th_bl)));;
agc "CORE_CORRECT_BL" SHA256_COMPRESS_HW_CORE_CORRECT_BL SHA256_COMPRESS_HW_CORE_CORRECT;;
Printf.printf "S062_CORE_CORRECT_BL_DONE\n%!";;


(* ========================================================================= *)
(* Session 063 — THEOREM 3/8: Windows NOIBT SUBROUTINE_CORRECT.               *)
(* Dev driver (run on warm s055cold; final claim cold-gated).                 *)
(*                                                                            *)
(* Structure mirrors the SysV hw NOIBT wrapper (same decode/core machinery)   *)
(* + mlkem_reduce's SIMD Windows xmm6-10 preservation + the nohw Windows       *)
(* wrapper's MP-bl-core / BIGSTEP-with-WINDOWS-exec / RA-re-derivation.  hw is *)
(* SIMPLER than nohw Windows: STATIC `sub $0x50` frame (no dynamic andq), so   *)
(* the delta/BITBLAST alignment dance is dropped.                              *)
(* ------------------------------------------------------------------------- *)

(* Windows K-base lea fold: lea sits at windows offset 42 (rip after = pc+49),  *)
(* disp = &(kk+4) - (&pc + -- &75) (Windows shim shifts the SysV -117 by 42).   *)
(* RIP_REL_ADDR_FOLD clause 2 with ofs=49, ofs2=75, tgt=kk+4 -> kk+128 = kptr.  *)
let SHA256_HW_WIN_LEA_FOLD = prove
 (`!pc kk. riprel32_within_bounds (kk + 128) (pc + 49)
     ==> word (val (word (pc + 49):int64) +
               val (word_sx (iword (&(kk + 4) - (&pc + -- &75)):int32):int64)):int64 =
         word_add (word kk) (word 128)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`pc:num`;`49`;`75`;`kk + 4`] RIP_REL_ADDR_FOLD) THEN
  REWRITE_TAC[ARITH_RULE `(kk + 4) + (49 + 75) = kk + 128`] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
  DISCH_THEN(fun th -> DISCH_THEN(fun bound ->
     REWRITE_TAC[MATCH_MP th bound])) THEN
  CONV_TAC WORD_RULE);;

Printf.printf "S063_WIN_LEA_FOLD hyps=%d\n%!" (List.length(hyp SHA256_HW_WIN_LEA_FOLD));;

(* ref for capturing the return-address fact at proof time (deref deferred). *)
let hw_win_ra_fact = ref TRUTH;;

(* ---- Windows NOIBT subroutine CORRECT (theorem 3 of 8), WQUAD form. ------- *)
let SHA256_COMPRESS_HW_NOIBT_WINDOWS_SUBROUTINE_CORRECT_WQUAD = prove
 (`!pc kk (sptr:int64) (dptr:int64) (H:int32 list) (m:num->int32 list)
     (num_blocks:num) stackpointer returnaddress.
     aligned 16 (word kk:int64) /\
     riprel32_within_bounds (kk + 128) (pc + 49) /\
     0 < num_blocks /\
     val (dptr:int64) + 64 * num_blocks < 2 EXP 64 /\
     nonoverlapping (word pc,896) (sptr,32) /\
     nonoverlapping (word pc,896) (word kk:int64,608) /\
     nonoverlapping (word pc,896) (dptr,64 * num_blocks) /\
     nonoverlapping (word pc,896) (word_sub stackpointer (word 96),104) /\
     nonoverlapping (sptr,32) (word_sub stackpointer (word 96),104) /\
     nonoverlapping (word kk:int64,608) (word_sub stackpointer (word 96),104) /\
     nonoverlapping (dptr,64 * num_blocks) (word_sub stackpointer (word 96),104) /\
     nonoverlapping (sptr,32) (word kk:int64,608) /\
     nonoverlapping (sptr,32) (dptr,64 * num_blocks)
     ==> ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_windows_tmc pc (kk + 4)) /\
            read RIP s = word pc /\
            read RSP s = stackpointer /\
            read (memory :> bytes64 stackpointer) s = returnaddress /\
            WINDOWS_C_ARGUMENTS [sptr; dptr; word num_blocks] s /\
            bytes_loaded s (word kk) K256 /\
            read (memory :> bytes128 sptr) s =
              WQUAD (EL 0 H) (EL 1 H) (EL 2 H) (EL 3 H) /\
            read (memory :> bytes128 (word_add sptr (word 16))) s =
              WQUAD (EL 4 H) (EL 5 H) (EL 6 H) (EL 7 H) /\
            (!j. j < num_blocks
                 ==> read (memory :> bytes128 (word_add dptr (word (64 * j)))) s =
                       WQUAD (word_bytereverse (EL 0 (m j))) (word_bytereverse (EL 1 (m j)))
                             (word_bytereverse (EL 2 (m j))) (word_bytereverse (EL 3 (m j))) /\
                     read (memory :> bytes128 (word_add dptr (word (64 * j + 16)))) s =
                       WQUAD (word_bytereverse (EL 4 (m j))) (word_bytereverse (EL 5 (m j)))
                             (word_bytereverse (EL 6 (m j))) (word_bytereverse (EL 7 (m j))) /\
                     read (memory :> bytes128 (word_add dptr (word (64 * j + 32)))) s =
                       WQUAD (word_bytereverse (EL 8 (m j))) (word_bytereverse (EL 9 (m j)))
                             (word_bytereverse (EL 10 (m j))) (word_bytereverse (EL 11 (m j))) /\
                     read (memory :> bytes128 (word_add dptr (word (64 * j + 48)))) s =
                       WQUAD (word_bytereverse (EL 12 (m j))) (word_bytereverse (EL 13 (m j)))
                             (word_bytereverse (EL 14 (m j))) (word_bytereverse (EL 15 (m j)))))
       (\s. read RIP s = returnaddress /\
            read RSP s = word_add stackpointer (word 8) /\
            read (memory :> bytes128 sptr) s =
              WQUAD (EL 0 (sha256_hash_blocks m H num_blocks))
                    (EL 1 (sha256_hash_blocks m H num_blocks))
                    (EL 2 (sha256_hash_blocks m H num_blocks))
                    (EL 3 (sha256_hash_blocks m H num_blocks)) /\
            read (memory :> bytes128 (word_add sptr (word 16))) s =
              WQUAD (EL 4 (sha256_hash_blocks m H num_blocks))
                    (EL 5 (sha256_hash_blocks m H num_blocks))
                    (EL 6 (sha256_hash_blocks m H num_blocks))
                    (EL 7 (sha256_hash_blocks m H num_blocks)))
       (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [memory :> bytes128 sptr;
                   memory :> bytes128 (word_add sptr (word 16))] ,,
        MAYCHANGE [memory :> bytes(word_sub stackpointer (word 96),96)])`,
  REWRITE_TAC[WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; WINDOWS_C_ARGUMENTS;
              fst SHA256_COMPRESS_HW_WINDOWS_EXEC] THEN
  REPLICATE_TAC 7 GEN_TAC THEN
  WORD_FORALL_OFFSET_TAC 96 THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SOME_FLAGS] THEN STRIP_TAC THEN
  (* the 6 kptr-relative alignments from aligned 16 (word kk) *)
  MP_TAC SHA256_HW_KPTR_ALIGN THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* preserve Windows callee-saved: RDI/RSI + xmm6..10 (= YMM6..10_SSE clobbered) *)
  ENSURES_PRESERVED_TAC "rdi_init" `RDI` THEN
  ENSURES_PRESERVED_TAC "rsi_init" `RSI` THEN
  ENSURES_PRESERVED_TAC "init_xmm6" `ZMM6 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm7" `ZMM7 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm8" `ZMM8 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm9" `ZMM9 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm10" `ZMM10 :> bottomhalf :> bottomhalf` THEN
  REWRITE_TAC[READ_ZMM_BOTTOM_QUARTER'] THEN
  REWRITE_TAC(map GSYM [YMM6;YMM7;YMM8;YMM9;YMM10]) THEN
  GHOST_INTRO_TAC `init_ymm6:int256` `read YMM6` THEN
  GHOST_INTRO_TAC `init_ymm7:int256` `read YMM7` THEN
  GHOST_INTRO_TAC `init_ymm8:int256` `read YMM8` THEN
  GHOST_INTRO_TAC `init_ymm9:int256` `read YMM9` THEN
  GHOST_INTRO_TAC `init_ymm10:int256` `read YMM10` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN
  ENSURES_INIT_TAC "s0" THEN
  (* derive the 16 K WQUAD rows + mask from the s0 bytes_loaded (word kk) K256 *)
  FIRST_ASSUM(fun th ->
    if (try name_of(rand(concl th)) = "K256" with _ -> false)
    then STRIP_ASSUME_TAC(MATCH_MP SHA256_HW_K256_WQUAD_READS
            (REWRITE_RULE[bytes_loaded] th))
    else NO_TAC) THEN
  (* step the 11-instr shim + 1-instr K-base lea (12 instrs to reach body). *)
  X86_STEPS_TAC SHA256_COMPRESS_HW_WINDOWS_EXEC (1--12) THEN
  (* capture RA fact at s12 (prologue end, pre-BIGSTEP). RA slot @ stackpointer+96. *)
  W(fun (asl,w) ->
     let isra (_,th) =
       let c = concl th in
       (try let _ = find_term (fun t -> try fst(dest_var t)="returnaddress"
                                        with _->false) c in is_eq c
        with _->false) in
     hw_win_ra_fact := snd (List.find isra asl); ALL_TAC) THEN
  (* fold RCX to kptr = word_add (word kk) (word 128). *)
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SHA256_HW_WIN_LEA_FOLD (ASSUME
     `riprel32_within_bounds (kk + 128) (pc + 49)`)]) THEN
  (* re-derive the bl-core body bytes_loaded at pc+42 (for the MP). *)
  SUBGOAL_THEN
   `bytes_loaded s12 (word (pc + 42))
       (sha256_compress_hw_bl_tmc (pc + 42) (kk + 4))`
  ASSUME_TAC THENL
   [REWRITE_TAC[sha256_compress_hw_bl_tmc] THEN
    MATCH_MP_TAC SHA256_HW_WIN_BODY_BRIDGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* apply the bl-core at pc:=pc+42, kbase:=kk+4, kptr:=kk+128. Normalize the
     (pc+42)+N offsets so the PRE/POST RIP match the stepped state. *)
  MP_TAC(REWRITE_RULE[ARITH_RULE `(pc + 42) + 7 = pc + 49`;
                      ARITH_RULE `(pc + 42) + 820 = pc + 862`]
    (SPECL
      [`pc + 42`; `kk + 4`; `word_add (word kk) (word 128):int64`;
       `sptr:int64`; `dptr:int64`; `H:int32 list`; `m:num->int32 list`;
       `num_blocks:num`]
      (REWRITE_RULE[SOME_FLAGS] SHA256_COMPRESS_HW_CORE_CORRECT_BL))) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN (NONOVERLAPPING_TAC ORELSE ASM_REWRITE_TAC[]);
    ALL_TAC] THEN
  (* BIGSTEP the core with the WINDOWS exec (program in memory). *)
  X86_BIGSTEP_TAC SHA256_COMPRESS_HW_WINDOWS_EXEC "s13" THENL
   [REWRITE_TAC[SHA256_HW_KADDR_NORM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* abbreviate the post-core (pre-epilogue) ymm values so the movups restores
     round-trip cleanly through the saved stack slots. *)
  MAP_EVERY ABBREV_TAC
   [`ymm6_epilog = read YMM6 s13`;
    `ymm7_epilog = read YMM7 s13`;
    `ymm8_epilog = read YMM8 s13`;
    `ymm9_epilog = read YMM9 s13`;
    `ymm10_epilog = read YMM10 s13`] THEN
  (* re-derive RA at s13 (deferred deref).  RA slot @ stackpointer+96, disjoint
     from the written frame [stackpointer, stackpointer+96). *)
  SUBGOAL_THEN
   `read (memory :> bytes64 (word_add stackpointer (word 96))) s13 = returnaddress`
  ASSUME_TAC THENL
   [W(fun (asl,w) -> ASSUME_TAC(!hw_win_ra_fact)) THEN
    FIRST_X_ASSUM(fun th ->
       if maychange_term(concl th) then MP_TAC th else NO_TAC) THEN
    REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
    REWRITE_TAC[GSYM SEQ_ASSOC] THEN
    PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
    CONV_TAC (TOP_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ASSIGNS_THM] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
    ASSUMPTION_STATE_UPDATE_TAC THEN
    DISCH_THEN(K ALL_TAC) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* step the 9-instr epilogue (movups restore x5 + add rsp + pop rsi/rdi + ret). *)
  X86_STEPS_TAC SHA256_COMPRESS_HW_WINDOWS_EXEC (14--22) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_ZMM_QUARTER]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_YMM_SSE_QUARTER]) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY MONOTONE_MAYCHANGE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  TRY(CONV_TAC WORD_BLAST) THEN
  TRY(CONV_TAC WORD_RULE));;

Printf.printf "S063_WIN_NOIBT_WQUAD hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_NOIBT_WINDOWS_SUBROUTINE_CORRECT_WQUAD))
  (List.length(frees(concl SHA256_COMPRESS_HW_NOIBT_WINDOWS_SUBROUTINE_CORRECT_WQUAD)));;
Printf.printf "S063_THM3_WQUAD_DONE\n%!";;

(* ========================================================================= *)
(* Session 063 — THEOREM 3/8 reshape: WQUAD -> nohw a..h/bytes32 interface.    *)
(* Mirrors the SysV reshape (SHA256_COMPRESS_HW_NOIBT_SUBROUTINE_CORRECT,      *)
(* L9623) via WQUAD_BYTES32/HW_EL8/hw_dword_fact, but the Windows write frame  *)
(* carries an extra MAYCHANGE [bytes(word_sub stackpointer (word 96),96)]      *)
(* component -> needs a Windows-specific FRAME_SUBSUMED.                        *)
(* ------------------------------------------------------------------------- *)

(* Windows frame: the 2 bytes128 WQUAD stores over statep are subsumed by the  *)
(* 32-byte region, with the WINDOWS ABI frame + stack-save region unchanged.   *)
let HW_WIN_FRAME_SUBSUMED = prove
 (`!statep:int64 stackpointer:int64.
     (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes128 statep;
                 memory :> bytes128 (word_add statep (word 16))] ,,
      MAYCHANGE [memory :> bytes(word_sub stackpointer (word 96),96)]) subsumed
     (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(statep,32)] ,,
      MAYCHANGE [memory :> bytes(word_sub stackpointer (word 96),96)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM SEQ_ASSOC] THEN
  MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL] THEN
  MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL] THEN
  MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL] THEN
  MATCH_ACCEPT_TAC HW_MEM_TAIL_SUB);;

Printf.printf "S063_WIN_FRAME_SUBSUMED hyps=%d\n%!" (List.length(hyp HW_WIN_FRAME_SUBSUMED));;

(* ---- Windows NOIBT subroutine CORRECT (theorem 3 of 8), nohw interface. ---- *)
let SHA256_COMPRESS_HW_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!pc kk (statep:int64) (dataptr:int64) (num_blocks:num)
     a b c d e f g h (m_fn:num->int32 list) stackpointer returnaddress.
     aligned 16 (word kk:int64) /\
     riprel32_within_bounds (kk + 128) (pc + 49) /\
     0 < num_blocks /\
     val (dataptr:int64) + 64 * num_blocks < 2 EXP 64 /\
     nonoverlapping (word pc,896) (statep,32) /\
     nonoverlapping (word pc,896) (word kk:int64,608) /\
     nonoverlapping (word pc,896) (dataptr,64 * num_blocks) /\
     nonoverlapping (word pc,896) (word_sub stackpointer (word 96),104) /\
     nonoverlapping (statep,32) (word_sub stackpointer (word 96),104) /\
     nonoverlapping (word kk:int64,608) (word_sub stackpointer (word 96),104) /\
     nonoverlapping (dataptr,64 * num_blocks) (word_sub stackpointer (word 96),104) /\
     nonoverlapping (statep,32) (word kk:int64,608) /\
     nonoverlapping (statep,32) (dataptr,64 * num_blocks)
     ==> ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_windows_tmc pc (kk + 4)) /\
            read RIP s = word pc /\
            read RSP s = stackpointer /\
            read (memory :> bytes64 stackpointer) s = returnaddress /\
            WINDOWS_C_ARGUMENTS [statep; dataptr; word num_blocks] s /\
            bytes_loaded s (word kk) K256 /\
            read (memory :> bytes32 statep) s = (a:int32) /\
            read (memory :> bytes32 (word_add statep (word 4))) s = (b:int32) /\
            read (memory :> bytes32 (word_add statep (word 8))) s = (c:int32) /\
            read (memory :> bytes32 (word_add statep (word 12))) s = (d:int32) /\
            read (memory :> bytes32 (word_add statep (word 16))) s = (e:int32) /\
            read (memory :> bytes32 (word_add statep (word 20))) s = (f:int32) /\
            read (memory :> bytes32 (word_add statep (word 24))) s = (g:int32) /\
            read (memory :> bytes32 (word_add statep (word 28))) s = (h:int32) /\
            (!i' j. i' < num_blocks /\ j < 16
                    ==> read (memory :> bytes32
                          (word_add dataptr (word (64*i' + 4*j)))) s =
                        word_bytereverse (EL j (m_fn i'):int32)))
       (\s. read RIP s = returnaddress /\
            read RSP s = word_add stackpointer (word 8) /\
            read (memory :> bytes32 statep) s =
              EL 0 (sha256_hash_blocks m_fn [a;b;c;d;e;f;g;h] num_blocks) /\
            read (memory :> bytes32 (word_add statep (word 4))) s =
              EL 1 (sha256_hash_blocks m_fn [a;b;c;d;e;f;g;h] num_blocks) /\
            read (memory :> bytes32 (word_add statep (word 8))) s =
              EL 2 (sha256_hash_blocks m_fn [a;b;c;d;e;f;g;h] num_blocks) /\
            read (memory :> bytes32 (word_add statep (word 12))) s =
              EL 3 (sha256_hash_blocks m_fn [a;b;c;d;e;f;g;h] num_blocks) /\
            read (memory :> bytes32 (word_add statep (word 16))) s =
              EL 4 (sha256_hash_blocks m_fn [a;b;c;d;e;f;g;h] num_blocks) /\
            read (memory :> bytes32 (word_add statep (word 20))) s =
              EL 5 (sha256_hash_blocks m_fn [a;b;c;d;e;f;g;h] num_blocks) /\
            read (memory :> bytes32 (word_add statep (word 24))) s =
              EL 6 (sha256_hash_blocks m_fn [a;b;c;d;e;f;g;h] num_blocks) /\
            read (memory :> bytes32 (word_add statep (word 28))) s =
              EL 7 (sha256_hash_blocks m_fn [a;b;c;d;e;f;g;h] num_blocks))
       (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [memory :> bytes(statep,32)] ,,
        MAYCHANGE [memory :> bytes(word_sub stackpointer (word 96),96)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* instantiate the WQUAD Windows theorem at H:=[a..h], m:=m_fn, sptr:=statep, *)
  (* then reframe to the bytes-region frame.                                    *)
  MP_TAC(SPECL
    [`pc:num`;`kk:num`;`statep:int64`;`dataptr:int64`;
     `[a;b;c;d;e;f;g;h]:int32 list`;`m_fn:num->int32 list`;
     `num_blocks:num`;`stackpointer:int64`;`returnaddress:int64`]
    SHA256_COMPRESS_HW_NOIBT_WINDOWS_SUBROUTINE_CORRECT_WQUAD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun wthm ->
    let wthm2 = MATCH_MP ENSURES_FRAME_SUBSUMED
                  (CONJ (SPECL [`statep:int64`;`stackpointer:int64`]
                           HW_WIN_FRAME_SUBSUMED) wthm) in
    MATCH_MP_TAC ENSURES_PREPOSTCONDITION_THM THEN
    EXISTS_TAC (rand(rator(rator(concl wthm2)))) THEN
    EXISTS_TAC (rand(rator(concl wthm2))) THEN
    REPEAT CONJ_TAC THENL
     [(* P' x ==> P x : nohw dwords ==> WQUAD reads *)
      GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
      REWRITE_TAC[HW_EL8; WQUAD_BYTES32] THEN
      REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REPEAT CONJ_TAC THEN
      TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      REWRITE_TAC[MSG_ADDR] THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY hw_dword_fact [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
      ASM_REWRITE_TAC[];
      (* Q x ==> Q' x : WQUAD post ==> nohw dwords *)
      GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[WQUAD_BYTES32; WORD_ADD_ASSOC_CONSTS]) THEN
      RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
      ASM_REWRITE_TAC[];
      (* ensures step P Q C : the reframed WQUAD theorem *)
      MATCH_ACCEPT_TAC wthm2]));;

Printf.printf "S063_WIN_NOIBT hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_NOIBT_WINDOWS_SUBROUTINE_CORRECT))
  (List.length(frees(concl SHA256_COMPRESS_HW_NOIBT_WINDOWS_SUBROUTINE_CORRECT)));;
Printf.printf "S063_THM3_RESHAPE_DONE\n%!";;

(* ========================================================================= *)
(* Session 063 — THEOREM 4/8: Windows IBT/endbr64 SUBROUTINE_CORRECT.          *)
(* Mirrors the SysV IBT hand-roll (SHA256_COMPRESS_HW_SUBROUTINE_CORRECT,      *)
(* L9762): the hw Windows lea has a NEGATIVE riprel (-75) that define_trimmed  *)
(* leaves UNSHIFTED, so windows_mc pc kk = [endbr] ++ windows_tmc pc kk (NOT   *)
(* (pc+4)); ADD_IBT_RULE ~bridge is hard-wired to the +4 shape and REJECTS it. *)
(* Hand-roll: mirror IBT_WRAP_TAC, MP thm-3 (Windows NOIBT) at pc:=pc+4, and    *)
(* fold the inner windows_tmc(pc+4)(kk+4) = windows_tmc pc kk via TMC_SHIFT.    *)
(* Geometry vs NOIBT: windows_mc, 900(=896+4), riprel (pc+53), and the endbr    *)
(* sits before the shim so the body starts 4 bytes later.                      *)
(* ------------------------------------------------------------------------- *)

(* windows_mc pc kk = APPEND [endbr64] (windows_tmc pc kk).  RHS is windows_tmc *)
(* **pc** (unshifted): the negative riprel is invariant under trimming.         *)
let SHA256_COMPRESS_HW_WINDOWS_MC_BRIDGE = prove
 (`!pc kk. sha256_compress_hw_windows_mc pc kk =
     APPEND [word 0xf3:byte; word 0x0f; word 0x1e; word 0xfa]
            (sha256_compress_hw_windows_tmc pc kk)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[sha256_compress_hw_windows_mc; sha256_compress_hw_windows_tmc;
              APPEND] THEN
  REWRITE_TAC[]);;

Printf.printf "S063_WIN_MC_BRIDGE hyps=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_WINDOWS_MC_BRIDGE));;

(* Shift-invariance of the trimmed windows image (K-lea disp = &kk-(&pc+ --75)  *)
(* invariant under (pc,kk)->(pc+4,kk+4)).  Lets the IBT hand-roll MP the NOIBT  *)
(* Windows wrapper at (pc+4,kk+4): its body windows_tmc(pc+4)(kk+4) folds to    *)
(* windows_tmc pc kk = the MC_BRIDGE body.                                      *)
let SHA256_COMPRESS_HW_WINDOWS_TMC_SHIFT = prove
 (`!pc kk. sha256_compress_hw_windows_tmc (pc + 4) (kk + 4) =
           sha256_compress_hw_windows_tmc pc kk`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sha256_compress_hw_windows_tmc] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
  REWRITE_TAC[INT_ARITH `(&kk + &4) - ((&pc + &4) + -- &75) =
                         &kk - (&pc + -- &75):int`]);;

Printf.printf "S063_WIN_TMC_SHIFT hyps=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_WINDOWS_TMC_SHIFT));;

(* ---- Windows IBT/endbr64 subroutine CORRECT (theorem 4 of 8). ------------ *)
(* Only windows_tmc->windows_mc, 896->900, (pc+49)->(pc+53), and the 104 stack *)
(* nonoverlap widen to match, plus riprel (pc+53).  code `windows_mc pc kk`,    *)
(* K256 @ `word kk` (kk unchanged, matching NOIBT).                            *)
let SHA256_COMPRESS_HW_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!pc kk (statep:int64) (dataptr:int64) (num_blocks:num)
     a b c d e f g h (m_fn:num->int32 list) stackpointer returnaddress.
     aligned 16 (word kk:int64) /\
     riprel32_within_bounds (kk + 128) (pc + 53) /\
     0 < num_blocks /\
     val (dataptr:int64) + 64 * num_blocks < 2 EXP 64 /\
     nonoverlapping (word pc,900) (statep,32) /\
     nonoverlapping (word pc,900) (word kk:int64,608) /\
     nonoverlapping (word pc,900) (dataptr,64 * num_blocks) /\
     nonoverlapping (word pc,900) (word_sub stackpointer (word 96),104) /\
     nonoverlapping (statep,32) (word_sub stackpointer (word 96),104) /\
     nonoverlapping (word kk:int64,608) (word_sub stackpointer (word 96),104) /\
     nonoverlapping (dataptr,64 * num_blocks) (word_sub stackpointer (word 96),104) /\
     nonoverlapping (statep,32) (word kk:int64,608) /\
     nonoverlapping (statep,32) (dataptr,64 * num_blocks)
     ==> ensures x86
       (\s. bytes_loaded s (word pc) (sha256_compress_hw_windows_mc pc kk) /\
            read RIP s = word pc /\
            read RSP s = stackpointer /\
            read (memory :> bytes64 stackpointer) s = returnaddress /\
            WINDOWS_C_ARGUMENTS [statep; dataptr; word num_blocks] s /\
            bytes_loaded s (word kk) K256 /\
            read (memory :> bytes32 statep) s = (a:int32) /\
            read (memory :> bytes32 (word_add statep (word 4))) s = (b:int32) /\
            read (memory :> bytes32 (word_add statep (word 8))) s = (c:int32) /\
            read (memory :> bytes32 (word_add statep (word 12))) s = (d:int32) /\
            read (memory :> bytes32 (word_add statep (word 16))) s = (e:int32) /\
            read (memory :> bytes32 (word_add statep (word 20))) s = (f:int32) /\
            read (memory :> bytes32 (word_add statep (word 24))) s = (g:int32) /\
            read (memory :> bytes32 (word_add statep (word 28))) s = (h:int32) /\
            (!i' j. i' < num_blocks /\ j < 16
                    ==> read (memory :> bytes32
                          (word_add dataptr (word (64*i' + 4*j)))) s =
                        word_bytereverse (EL j (m_fn i'):int32)))
       (\s. read RIP s = returnaddress /\
            read RSP s = word_add stackpointer (word 8) /\
            read (memory :> bytes32 statep) s =
              EL 0 (sha256_hash_blocks m_fn [a;b;c;d;e;f;g;h] num_blocks) /\
            read (memory :> bytes32 (word_add statep (word 4))) s =
              EL 1 (sha256_hash_blocks m_fn [a;b;c;d;e;f;g;h] num_blocks) /\
            read (memory :> bytes32 (word_add statep (word 8))) s =
              EL 2 (sha256_hash_blocks m_fn [a;b;c;d;e;f;g;h] num_blocks) /\
            read (memory :> bytes32 (word_add statep (word 12))) s =
              EL 3 (sha256_hash_blocks m_fn [a;b;c;d;e;f;g;h] num_blocks) /\
            read (memory :> bytes32 (word_add statep (word 16))) s =
              EL 4 (sha256_hash_blocks m_fn [a;b;c;d;e;f;g;h] num_blocks) /\
            read (memory :> bytes32 (word_add statep (word 20))) s =
              EL 5 (sha256_hash_blocks m_fn [a;b;c;d;e;f;g;h] num_blocks) /\
            read (memory :> bytes32 (word_add statep (word 24))) s =
              EL 6 (sha256_hash_blocks m_fn [a;b;c;d;e;f;g;h] num_blocks) /\
            read (memory :> bytes32 (word_add statep (word 28))) s =
              EL 7 (sha256_hash_blocks m_fn [a;b;c;d;e;f;g;h] num_blocks))
       (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [memory :> bytes(statep,32)] ,,
        MAYCHANGE [memory :> bytes(word_sub stackpointer (word 96),96)])`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SHA256_COMPRESS_HW_WINDOWS_MC_BRIDGE] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; SOME_FLAGS;
              C_ARGUMENTS; C_RETURN; WINDOWS_C_ARGUMENTS;
              WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN
  IBT_WRAP_TAC
   (W (fun (asl,w) ->
      let avs,_ =
        strip_forall (concl SHA256_COMPRESS_HW_NOIBT_WINDOWS_SUBROUTINE_CORRECT) in
      (* thm 3 states code `windows_tmc pc (kk+4)` and K256 @ word kk; MP at    *)
      (* pc:=pc+4 (kk UNCHANGED) gives code windows_tmc (pc+4) (kk+4), which     *)
      (* WINDOWS_TMC_SHIFT folds to windows_tmc pc kk = the MC_BRIDGE body.      *)
      let new_avs = map (fun v ->
        if is_var v && name_of v = "pc" then mk_binary "+" (v,`4`)
        else v) avs in
      MP_TAC (REWRITE_RULE[C_ARGUMENTS; C_RETURN; WINDOWS_C_ARGUMENTS;
                            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                            WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                            SOME_FLAGS; SHA256_COMPRESS_HW_WINDOWS_TMC_SHIFT]
              (SPECL new_avs SHA256_COMPRESS_HW_NOIBT_WINDOWS_SUBROUTINE_CORRECT)) THEN
      CONV_TAC(ONCE_DEPTH_CONV
        (REWR_CONV(ARITH_RULE `(pc + 4) + n:num = pc + (n + 4)`) THENC
         RAND_CONV NUM_ADD_CONV)) THEN
      REWRITE_TAC[
        WORD_RULE `word(pc+4):int64 = word_add (word pc) (word 4)`] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
      REPEAT CONJ_TAC THEN
      TRY (FIRST_X_ASSUM ACCEPT_TAC) THEN
      NONOVERLAPPING_TAC)));;

Printf.printf "S063_WIN_IBT hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_WINDOWS_SUBROUTINE_CORRECT))
  (List.length(frees(concl SHA256_COMPRESS_HW_WINDOWS_SUBROUTINE_CORRECT)));;
Printf.printf "S063_THM4_DONE\n%!";;

(* ========================================================================= *)
(* Session 063 — CORE_SAFE_BL: the SysV CORE_SAFE re-stated over bl_tmc        *)
(* (= BUTLAST sysv_tmc), the SAFE analog of CORE_CORRECT_BL.  Needed by the    *)
(* Windows SAFE wrappers (thms 7-8): the Windows image lacks the SysV trailing *)
(* `ret`, so only BUTLAST(sysv_tmc) is a subprogram of windows_tmc.            *)
(*                                                                            *)
(* Statement = bl_of_stmt_reg(concl CORE_SAFE) (tmc->bl_tmc, 825->820); proof  *)
(* = the committed CORE_SAFE tactic replayed VERBATIM with                     *)
(* SHA256_COMPRESS_HW_EXEC -> SHA256_COMPRESS_HW_BL_EXEC (bl_tmc decodes rows   *)
(* [0,820) identically, so all three X86_STEPS_TAC segments replay).           *)
(* ------------------------------------------------------------------------- *)

let SHA256_COMPRESS_HW_CORE_SAFE_BL = prove
 (bl_of_stmt_reg (concl SHA256_COMPRESS_HW_CORE_SAFE),
  CONCRETIZE_F_EVENTS_TAC sha256_hw_safe_f_events_shape THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `num_blocks:num` `pc + 0x38` `pc + 0x312`
    sha256_hw_safe_loop_inv THEN
  REPEAT CONJ_TAC THENL [
    ASM_ARITH_TAC;
    MP_TAC SHA256_HW_KPTR_ALIGN THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC SHA256_COMPRESS_HW_BL_EXEC (1--10) THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; ADD_CLAUSES; SUB_0] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT (CONJ_TAC THENL
     [ (CONV_TAC WORD_RULE ORELSE ASM_REWRITE_TAC[]); ALL_TAC ]) THEN
    SAFE_META_EXISTS_TAC allowed_vars_e THEN
    CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
    W (fun (asl,w) ->
      (if is_conj w then (CONJ_TAC THENL [ FULL_UNIFY_F_EVENTS_TAC; ALL_TAC ])
       else ALL_TAC) THEN
      REWRITE_TAC[SHA256_HW_KADDR_NORM] THEN
      DISCHARGE_MEMACCESS_INBOUNDS_TAC);
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `num_blocks < 2 EXP 64` ASSUME_TAC THENL
     [TRANS_TAC LET_TRANS `val (dptr:int64) + 64 * num_blocks` THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    MP_TAC SHA256_HW_KPTR_ALIGN THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC SHA256_COMPRESS_HW_BL_EXEC (1--170) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT (CONJ_TAC THENL
     [ (ASM_SIMP_TAC[SHA256_HW_RSI_STEP; SHA256_HW_RDX_STEP] THEN NO_TAC) ORELSE
       (CONV_TAC WORD_RULE) ORELSE
       (ASM_SIMP_TAC[SHA256_HW_ZF_EXIT] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[]) ORELSE
       ASM_REWRITE_TAC[]; ALL_TAC ]) THEN
    SAFE_META_EXISTS_TAC allowed_vars_e THEN
    CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
    W (fun (asl,w) ->
      (if is_conj w then (CONJ_TAC THENL [ FULL_UNIFY_F_EVENTS_TAC; ALL_TAC ])
       else ALL_TAC) THEN
      REWRITE_TAC[SHA256_HW_KADDR_NORM] THEN
      DISCHARGE_MEMACCESS_INBOUNDS_TAC);
    ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC SHA256_COMPRESS_HW_BL_EXEC (1--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SAFE_META_EXISTS_TAC allowed_vars_e THEN
    CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
    W (fun (asl,w) ->
      (if is_conj w then (CONJ_TAC THENL [ FULL_UNIFY_F_EVENTS_TAC; ALL_TAC ])
       else ALL_TAC) THEN
      REWRITE_TAC[SHA256_HW_KADDR_NORM] THEN
      DISCHARGE_MEMACCESS_INBOUNDS_TAC) ]);;

Printf.printf "S063_CORE_SAFE_BL hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_CORE_SAFE_BL))
  (List.length(frees(concl SHA256_COMPRESS_HW_CORE_SAFE_BL)));;
(* aconv gate against the mechanical bl-image of CORE_SAFE. *)
Printf.printf "S063_CORE_SAFE_BL GATE %s\n%!"
  (if aconv (concl SHA256_COMPRESS_HW_CORE_SAFE_BL)
            (bl_of_stmt_reg(concl SHA256_COMPRESS_HW_CORE_SAFE))
   then "PASS" else "*** FAIL ***");;
Printf.printf "S063_CORE_SAFE_BL_DONE\n%!";;

(* ========================================================================= *)
(* Phase 9 -- Windows NOIBT subroutine SAFE (theorem 7 of 8).                *)
(*                                                                           *)
(* Fusion of thm 3 (Windows NOIBT CORRECT prologue/epilogue + xmm6-10        *)
(* preservation over CORE_SAFE_BL) with the SysV SAFE closer (thm 5).  The   *)
(* f_events SP-argument is the FRAME BASE word_sub stackpointer (word 96)    *)
(* so WORD_FORALL_OFFSET_TAC 96 normalizes it to the loop-bound var, letting *)
(* the frame-relative movups spill/restore events abstract.  Final goal =    *)
(* (exists e2. events /\ inbounds) /\ 5 xmm round-trip identities: split and *)
(* discharge the safety existential, WORD_BLAST the xmm block.               *)
(* ------------------------------------------------------------------------- *)
(* ========================================================================= *)
(* Session 064 — THEOREM 7/8: Windows NOIBT SUBROUTINE_SAFE.                   *)
(* Fusion of thm 3 (Windows NOIBT CORRECT: 12-instr shim+lea prologue,         *)
(* xmm6-10 preservation, s13 BIGSTEP over CORE_SAFE_BL, 9-instr epilogue) with *)
(* the SysV SAFE closer (thm 5).  hw is SIMPLER than nohw Windows SAFE: static *)
(* sub 0x50 (no delta/BITBLAST), plain X86_STEPS_TAC (no C8).                   *)
(* Read set = [statep,32; dataptr,64*nb; word kk,608; sp-96,104] SUPERSET      *)
(* write set = [statep,32; sp-96,96].                                          *)
(*                                                                             *)
(* s063 defect fixed: (1) the earlier driver had backtick-quoted terms INSIDE  *)
(* the theorem literal comment -> parse error; (2) the f_events SP-argument     *)
(* must be the FRAME BASE word_sub stackpointer (word 96) (WORD_FORALL_OFFSET_  *)
(* TAC 96 normalizes it to the bound var x, so the frame-relative spill events  *)
(* abstract), NOT bare stackpointer (= word_add x (word 96), non-abstractable). *)
(* ------------------------------------------------------------------------- *)

let hw_win_ra_fact_safe = ref TRUTH;;
let sha256_hw_e_wrap_win = ref `e:(uarch_event)list`;;

let SHA256_COMPRESS_HW_NOIBT_WINDOWS_SUBROUTINE_SAFE = prove
 (`exists f_events.
    forall e pc kk (statep:int64) (dataptr:int64) (num_blocks:num)
           stackpointer returnaddress.
        aligned 16 (word kk:int64) /\
        riprel32_within_bounds (kk + 128) (pc + 49) /\
        0 < num_blocks /\
        val (dataptr:int64) + 64 * num_blocks < 2 EXP 64 /\
        nonoverlapping (word pc,896) (statep,32) /\
        nonoverlapping (word pc,896) (word kk:int64,608) /\
        nonoverlapping (word pc,896) (dataptr,64 * num_blocks) /\
        nonoverlapping (word pc,896) (word_sub stackpointer (word 96),104) /\
        nonoverlapping (statep,32) (word_sub stackpointer (word 96),104) /\
        nonoverlapping (word kk:int64,608) (word_sub stackpointer (word 96),104) /\
        nonoverlapping (dataptr,64 * num_blocks) (word_sub stackpointer (word 96),104) /\
        nonoverlapping (statep,32) (word kk:int64,608) /\
        nonoverlapping (statep,32) (dataptr,64 * num_blocks)
        ==> ensures x86
            (\s. bytes_loaded s (word pc) (sha256_compress_hw_windows_tmc pc (kk + 4)) /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 WINDOWS_C_ARGUMENTS [statep; dataptr; word num_blocks] s /\
                 bytes_loaded s (word kk) K256 /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events dataptr statep num_blocks kk pc
                             (word_sub stackpointer (word 96)) returnaddress /\
                      memaccess_inbounds e2
                        [statep:int64,32; dataptr:int64,64 * num_blocks;
                         word kk:int64,608; word_sub stackpointer (word 96):int64,104]
                        [statep:int64,32; word_sub stackpointer (word 96):int64,96]))
            (MAYCHANGE [RSP] ,,
             WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(statep,32)] ,,
             MAYCHANGE [memory :> bytes(word_sub stackpointer (word 96),96)] ,,
             MAYCHANGE [events])`,
  REWRITE_TAC[fst SHA256_COMPRESS_HW_WINDOWS_EXEC] THEN
  REWRITE_TAC[WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ASSUME_CALLEE_SAFETY_TAC SHA256_COMPRESS_HW_CORE_SAFE_BL "HCORE" THEN
  META_EXISTS_TAC THEN
  REWRITE_TAC[WINDOWS_C_ARGUMENTS] THEN
  REPLICATE_TAC 6 GEN_TAC THEN
  WORD_FORALL_OFFSET_TAC 96 THEN
  REWRITE_TAC[HW_K_BYTES_FORM] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC SHA256_HW_KPTR_ALIGN THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ENSURES_PRESERVED_TAC "rdi_init" `RDI` THEN
  ENSURES_PRESERVED_TAC "rsi_init" `RSI` THEN
  ENSURES_PRESERVED_TAC "init_xmm6" `ZMM6 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm7" `ZMM7 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm8" `ZMM8 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm9" `ZMM9 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm10" `ZMM10 :> bottomhalf :> bottomhalf` THEN
  REWRITE_TAC[READ_ZMM_BOTTOM_QUARTER'] THEN
  REWRITE_TAC(map GSYM [YMM6;YMM7;YMM8;YMM9;YMM10]) THEN
  GHOST_INTRO_TAC `init_ymm6:int256` `read YMM6` THEN
  GHOST_INTRO_TAC `init_ymm7:int256` `read YMM7` THEN
  GHOST_INTRO_TAC `init_ymm8:int256` `read YMM8` THEN
  GHOST_INTRO_TAC `init_ymm9:int256` `read YMM9` THEN
  GHOST_INTRO_TAC `init_ymm10:int256` `read YMM10` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC SHA256_COMPRESS_HW_WINDOWS_EXEC (1--12) THEN
  (* capture RA fact at s12 (prologue end). *)
  W(fun (asl,w) ->
     let isra (_,th) =
       let c = concl th in
       (try let _ = find_term (fun t -> try fst(dest_var t)="returnaddress"
                                        with _->false) c in is_eq c
        with _->false) in
     hw_win_ra_fact_safe := snd (List.find isra asl); ALL_TAC) THEN
  (* fold RCX to kptr = kk+128. *)
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SHA256_HW_WIN_LEA_FOLD (ASSUME
     `riprel32_within_bounds (kk + 128) (pc + 49)`)]) THEN
  (* capture the s12 events trace to feed the core SAFE's e argument. *)
  W(fun (asl,w) ->
     let _,th = find (fun (_,th) ->
        let c = concl th in
        is_eq c && string_of_term(lhand c) = "read events s12") asl in
     sha256_hw_e_wrap_win := rhs(concl th); ALL_TAC) THEN
  (* re-derive the bl-core body bytes_loaded at pc+42. *)
  SUBGOAL_THEN
   `bytes_loaded s12 (word (pc + 42))
       (sha256_compress_hw_bl_tmc (pc + 42) (kk + 4))`
  ASSUME_TAC THENL
   [REWRITE_TAC[sha256_compress_hw_bl_tmc] THEN
    MATCH_MP_TAC SHA256_HW_WIN_BODY_BRIDGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* MP the bl-core SAFE (HCORE) at pc:=pc+42, kbase:=kk+4, kptr:=kk+128, e:=s12 trace. *)
  W(fun (asl,w) ->
    let _,hcore = find (fun (nm,_) -> nm="HCORE") asl in
    let specth = SPECL
      [ `pc + 42`; `kk + 4`; `kk:num`; `statep:int64`;
        `dataptr:int64`; `num_blocks:num`; !sha256_hw_e_wrap_win ] hcore in
    MP_TAC (REWRITE_RULE[ARITH_RULE `(pc + 42) + 7 = pc + 49`;
                         ARITH_RULE `(pc + 42) + 820 = pc + 862`; IMP_IMP] specth)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN (NONOVERLAPPING_TAC ORELSE ASM_REWRITE_TAC[]); ALL_TAC] THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  X86_BIGSTEP_TAC SHA256_COMPRESS_HW_WINDOWS_EXEC "s13" THEN
  MAP_EVERY ABBREV_TAC
   [`ymm6_epilog = read YMM6 s13`;
    `ymm7_epilog = read YMM7 s13`;
    `ymm8_epilog = read YMM8 s13`;
    `ymm9_epilog = read YMM9 s13`;
    `ymm10_epilog = read YMM10 s13`] THEN
  (* re-derive RA at s13 (RA slot @ stackpointer+96). *)
  SUBGOAL_THEN
   `read (memory :> bytes64 (word_add stackpointer (word 96))) s13 = returnaddress`
  ASSUME_TAC THENL
   [W(fun (asl,w) -> ASSUME_TAC(!hw_win_ra_fact_safe)) THEN
    FIRST_X_ASSUM(fun th ->
       if maychange_term(concl th) then MP_TAC th else NO_TAC) THEN
    REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
    REWRITE_TAC[GSYM SEQ_ASSOC] THEN
    PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
    CONV_TAC (TOP_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ASSIGNS_THM] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
    ASSUMPTION_STATE_UPDATE_TAC THEN
    DISCH_THEN(K ALL_TAC) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X86_STEPS_TAC SHA256_COMPRESS_HW_WINDOWS_EXEC (14--22) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_ZMM_QUARTER]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_YMM_SSE_QUARTER]) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  (* Goal shape (diag s064): (exists e2. events /\ e2=f_events.. /\ inbounds) /\   *)
  (* (5 xmm round-trip identities).  RIP/RSP already closed by ASM_REWRITE_TAC.    *)
  (* Split the safety existential from the xmm block; discharge each.              *)
  CONJ_TAC THENL
   [ DISCHARGE_SAFETY_PROPERTY_TAC;
     REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_BLAST) THEN TRY(CONV_TAC WORD_RULE) ]);;

Printf.printf "S064_WIN_NOIBT_SAFE hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_NOIBT_WINDOWS_SUBROUTINE_SAFE))
  (List.length(frees(concl SHA256_COMPRESS_HW_NOIBT_WINDOWS_SUBROUTINE_SAFE)));;
Printf.printf "S064_THM7_DONE\n%!";;

(* ========================================================================= *)
(* Phase 9 -- Windows IBT/endbr64 subroutine SAFE (theorem 8 of 8).          *)
(*                                                                           *)
(* SAFE analogue of thm 4 (Windows IBT CORRECT), built like thm 6 (SysV IBT  *)
(* SAFE) but with the WINDOWS bridge/shift.  windows_mc pc kk =              *)
(* [endbr]++windows_tmc pc kk with a NEGATIVE riprel UNSHIFTED, so           *)
(* ADD_IBT_RULE's +4 shape rejects it -> hand-roll: ADD_IBT_OPEN_EXISTS      *)
(* (opens the `exists f_events` head) + IBT_WRAP_TAC + MP thm 7 at pc:=pc+4  *)
(* folding windows_tmc(pc+4)(kk+4)=windows_tmc pc kk via WINDOWS_TMC_SHIFT.   *)
(* Spec = thm-7 spec, IBT deltas applied to the exists/forall-STRIPPED body   *)
(* (kk FREE) then re-quantified -- a whole-concl subst would refuse kk+4->kk  *)
(* to avoid capturing the bound kk.                                          *)
(* ------------------------------------------------------------------------- *)
(* ========================================================================= *)
(* Session 064 — THEOREM 8/8: Windows IBT/endbr64 SUBROUTINE_SAFE.             *)
(* SAFE analogue of thm 4 (Windows IBT CORRECT): mirror the SysV IBT SAFE      *)
(* hand-roll (thm 6, SHA256_COMPRESS_HW_SUBROUTINE_SAFE) but with the WINDOWS  *)
(* bridge/shift.  The hw Windows lea has a NEGATIVE riprel (-75) that          *)
(* define_trimmed leaves UNSHIFTED, so windows_mc pc kk = [endbr]++windows_tmc *)
(* pc kk (NOT (pc+4)); ADD_IBT_RULE's hard-wired +4 shape REJECTS it, so we    *)
(* HAND-ROLL: ADD_IBT_OPEN_EXISTS (handles the `exists f_events` head, feeding  *)
(* a witnessed forall th_inner) + IBT_WRAP_TAC + MP thm 7 at pc:=pc+4, folding  *)
(* windows_tmc(pc+4)(kk+4) = windows_tmc pc kk via WINDOWS_TMC_SHIFT.           *)
(* Geometry vs NOIBT SAFE: windows_mc, 900(=896+4), riprel (pc+53).            *)
(* ------------------------------------------------------------------------- *)

(* thm-8 spec = thm-7 spec with the IBT deltas.  As with thm3->thm4 and       *)
(* thm5->thm6, the code changes windows_tmc pc (kk+4) -> windows_mc pc kk      *)
(* (K-base kk, NOT kk+4 — the endbr-prefixed image is keyed at kk), riprel     *)
(* (pc+49)->(pc+53), size 896->900.  Constructed via subst on the exists/      *)
(* forall-STRIPPED body (so `kk` is FREE, not bound — a whole-concl subst       *)
(* refuses `kk+4 -> kk` to avoid capturing the bound kk, leaving kk+4 in the    *)
(* code), then re-quantified with the ORIGINAL binder structure.               *)
let sha256_hw_win_safe_ibt_spec =
  let fev,fbody = dest_exists (concl SHA256_COMPRESS_HW_NOIBT_WINDOWS_SUBROUTINE_SAFE) in
  let bvars,ibody = strip_forall fbody in
  let ibody' = subst [`sha256_compress_hw_windows_mc`,`sha256_compress_hw_windows_tmc`;
                      `kk:num`,`kk + 4`; `900`,`896`; `53`,`49`] ibody in
  mk_exists(fev, list_mk_forall(bvars, ibody'));;

let SHA256_COMPRESS_HW_WINDOWS_SUBROUTINE_SAFE = prove
 (sha256_hw_win_safe_ibt_spec,
  REWRITE_TAC[SHA256_COMPRESS_HW_WINDOWS_MC_BRIDGE] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; SOME_FLAGS;
              C_ARGUMENTS; C_RETURN; WINDOWS_C_ARGUMENTS;
              WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ADD_IBT_OPEN_EXISTS SHA256_COMPRESS_HW_NOIBT_WINDOWS_SUBROUTINE_SAFE
   (fun th_inner ->
    REPEAT GEN_TAC THEN
    REWRITE_TAC[SHA256_COMPRESS_HW_WINDOWS_MC_BRIDGE] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; SOME_FLAGS;
                C_ARGUMENTS; C_RETURN; WINDOWS_C_ARGUMENTS;
                WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT STRIP_TAC THEN
    IBT_WRAP_TAC
     (W (fun (asl,w) ->
        let avs,_ = strip_forall (concl th_inner) in
        let new_avs = map (fun v ->
          if is_var v && name_of v = "pc" then mk_binary "+" (v,`4`) else v)
          avs in
        MP_TAC (REWRITE_RULE[C_ARGUMENTS; C_RETURN; WINDOWS_C_ARGUMENTS;
                              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                              WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                              SOME_FLAGS; SHA256_COMPRESS_HW_WINDOWS_TMC_SHIFT]
                (SPECL new_avs th_inner)) THEN
        CONV_TAC(ONCE_DEPTH_CONV
          (REWR_CONV(ARITH_RULE `(pc + 4) + n:num = pc + (n + 4)`) THENC
           RAND_CONV NUM_ADD_CONV)) THEN
        REWRITE_TAC[
          WORD_RULE `word(pc+4):int64 = word_add (word pc) (word 4)`] THEN
        DISCH_THEN MATCH_MP_TAC THEN
        POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
        REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
        REPEAT CONJ_TAC THEN
        TRY (FIRST_X_ASSUM ACCEPT_TAC) THEN
        NONOVERLAPPING_TAC))));;

Printf.printf "S064_WIN_IBT_SAFE hyps=%d frees=%d\n%!"
  (List.length(hyp SHA256_COMPRESS_HW_WINDOWS_SUBROUTINE_SAFE))
  (List.length(frees(concl SHA256_COMPRESS_HW_WINDOWS_SUBROUTINE_SAFE)));;
Printf.printf "S064_THM8_DONE\n%!";;
