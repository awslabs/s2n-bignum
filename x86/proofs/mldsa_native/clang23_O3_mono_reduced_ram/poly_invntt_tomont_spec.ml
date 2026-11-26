(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Inverse number-theoretic transform with the factor mont / 256: the        *)
(* statement. This is the code for mldsa_poly_invntt_tomont                  *)
(* (mld_poly_invntt_tomont in poly.c, which calls the _c version) from       *)
(* mldsa-native's portable C implementation compiled by clang 23 with -O3 as *)
(* one translation unit with MLD_CONFIG_REDUCE_RAM (see                      *)
(* mldsa_native/README.md). clang has unrolled the loops over the layers:    *)
(* layers 8 to 4 are scalar loops with a block of 2 to 32 coefficients per   *)
(* iteration, which read the zetas from the table mld_zetas; layers 3 to 1   *)
(* are SSE loops with the zeta of a block in constants (mldsa_poly_invntt_   *)
(* tomont_consts, 448 bytes of read-only data); a last loop scales each      *)
(* coefficient with a Montgomery multiplication by 41978. It is verified in  *)
(* the whole image (see libmldsa.ml) against mld_poly_invntt_tomont of       *)
(* common/mldsa_native_poly.ml. It is also shown to be constant time and     *)
(* memory safe: the readable memory includes the constants.                  *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_poly.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa_poly_invntt_tomont:
       +0x0: push    %rbx
       +0x1: lea     0x1c744(%rip),%rcx
       +0x8: mov     $0xfffffffffffffffe,%rdx
       +0xf: movabs  $0x380200100000000,%rax
      +0x19: nopl    0x0(%rax)
      +0x20: xor     %esi,%esi
      +0x22: sub     (%rcx),%esi
      +0x24: movslq  %esi,%rsi
      +0x27: mov     0x8(%rdi,%rdx,4),%r8d
      +0x2c: mov     0xc(%rdi,%rdx,4),%r9d
      +0x31: lea     (%r9,%r8,1),%r10d
      +0x35: mov     %r10d,0x8(%rdi,%rdx,4)
      +0x3a: sub     %r9d,%r8d
      +0x3d: movslq  %r8d,%r8
      +0x40: imul    %rsi,%r8
      +0x44: mov     %r8,%rsi
      +0x47: imul    %rax,%rsi
      +0x4b: sar     $0x20,%rsi
      +0x4f: imul    $0xffffffffff801fff,%rsi,%rsi
      +0x56: add     %r8,%rsi
      +0x59: shr     $0x20,%rsi
      +0x5d: mov     %esi,0xc(%rdi,%rdx,4)
      +0x61: add     $0xfffffffffffffffc,%rcx
      +0x65: add     $0x2,%rdx
      +0x69: cmp     $0xfe,%rdx
      +0x70: jb      <mldsa_poly_invntt_tomont+0x20>
      +0x72: lea     0x1c4d3(%rip),%rcx
      +0x79: mov     $0xfffffffffffffffc,%rdx
      +0x80: xor     %esi,%esi
      +0x82: sub     (%rcx),%esi
      +0x84: movslq  %esi,%rsi
      +0x87: mov     0x18(%rdi,%rdx,4),%r8d
      +0x8c: mov     0x10(%rdi,%rdx,4),%r9d
      +0x91: mov     0x14(%rdi,%rdx,4),%r10d
      +0x96: lea     (%r8,%r9,1),%r11d
      +0x9a: mov     %r11d,0x10(%rdi,%rdx,4)
      +0x9f: sub     %r8d,%r9d
      +0xa2: movslq  %r9d,%r8
      +0xa5: imul    %rsi,%r8
      +0xa9: mov     %r8,%r9
      +0xac: imul    %rax,%r9
      +0xb0: sar     $0x20,%r9
      +0xb4: imul    $0xffffffffff801fff,%r9,%r9
      +0xbb: add     %r8,%r9
      +0xbe: shr     $0x20,%r9
      +0xc2: mov     %r9d,0x18(%rdi,%rdx,4)
      +0xc7: mov     0x1c(%rdi,%rdx,4),%r8d
      +0xcc: lea     (%r8,%r10,1),%r9d
      +0xd0: mov     %r9d,0x14(%rdi,%rdx,4)
      +0xd5: sub     %r8d,%r10d
      +0xd8: movslq  %r10d,%r8
      +0xdb: imul    %rsi,%r8
      +0xdf: mov     %r8,%rsi
      +0xe2: imul    %rax,%rsi
      +0xe6: sar     $0x20,%rsi
      +0xea: imul    $0xffffffffff801fff,%rsi,%rsi
      +0xf1: add     %r8,%rsi
      +0xf4: shr     $0x20,%rsi
      +0xf8: mov     %esi,0x1c(%rdi,%rdx,4)
      +0xfc: add     $0xfffffffffffffffc,%rcx
     +0x100: add     $0x4,%rdx
     +0x104: cmp     $0xfc,%rdx
     +0x10b: jb      <mldsa_poly_invntt_tomont+0x80>
     +0x111: lea     0x1c334(%rip),%rcx
     +0x118: mov     $0xfffffffffffffff8,%rdx
     +0x11f: nop     
     +0x120: xor     %esi,%esi
     +0x122: sub     (%rcx),%esi
     +0x124: movslq  %esi,%rsi
     +0x127: mov     0x30(%rdi,%rdx,4),%r8d
     +0x12c: mov     0x20(%rdi,%rdx,4),%r9d
     +0x131: mov     0x24(%rdi,%rdx,4),%r10d
     +0x136: lea     (%r8,%r9,1),%r11d
     +0x13a: mov     %r11d,0x20(%rdi,%rdx,4)
     +0x13f: sub     %r8d,%r9d
     +0x142: movslq  %r9d,%r8
     +0x145: imul    %rsi,%r8
     +0x149: mov     %r8,%r9
     +0x14c: imul    %rax,%r9
     +0x150: sar     $0x20,%r9
     +0x154: imul    $0xffffffffff801fff,%r9,%r9
     +0x15b: add     %r8,%r9
     +0x15e: shr     $0x20,%r9
     +0x162: mov     %r9d,0x30(%rdi,%rdx,4)
     +0x167: mov     0x34(%rdi,%rdx,4),%r8d
     +0x16c: lea     (%r8,%r10,1),%r9d
     +0x170: mov     %r9d,0x24(%rdi,%rdx,4)
     +0x175: sub     %r8d,%r10d
     +0x178: movslq  %r10d,%r8
     +0x17b: imul    %rsi,%r8
     +0x17f: mov     %r8,%r9
     +0x182: imul    %rax,%r9
     +0x186: sar     $0x20,%r9
     +0x18a: imul    $0xffffffffff801fff,%r9,%r9
     +0x191: add     %r8,%r9
     +0x194: shr     $0x20,%r9
     +0x198: mov     %r9d,0x34(%rdi,%rdx,4)
     +0x19d: mov     0x28(%rdi,%rdx,4),%r8d
     +0x1a2: mov     0x38(%rdi,%rdx,4),%r9d
     +0x1a7: lea     (%r9,%r8,1),%r10d
     +0x1ab: mov     %r10d,0x28(%rdi,%rdx,4)
     +0x1b0: sub     %r9d,%r8d
     +0x1b3: movslq  %r8d,%r8
     +0x1b6: imul    %rsi,%r8
     +0x1ba: mov     %r8,%r9
     +0x1bd: imul    %rax,%r9
     +0x1c1: sar     $0x20,%r9
     +0x1c5: imul    $0xffffffffff801fff,%r9,%r9
     +0x1cc: add     %r8,%r9
     +0x1cf: shr     $0x20,%r9
     +0x1d3: mov     %r9d,0x38(%rdi,%rdx,4)
     +0x1d8: mov     0x2c(%rdi,%rdx,4),%r8d
     +0x1dd: mov     0x3c(%rdi,%rdx,4),%r9d
     +0x1e2: lea     (%r9,%r8,1),%r10d
     +0x1e6: mov     %r10d,0x2c(%rdi,%rdx,4)
     +0x1eb: sub     %r9d,%r8d
     +0x1ee: movslq  %r8d,%r8
     +0x1f1: imul    %rsi,%r8
     +0x1f5: mov     %r8,%rsi
     +0x1f8: imul    %rax,%rsi
     +0x1fc: sar     $0x20,%rsi
     +0x200: imul    $0xffffffffff801fff,%rsi,%rsi
     +0x207: add     %r8,%rsi
     +0x20a: shr     $0x20,%rsi
     +0x20e: mov     %esi,0x3c(%rdi,%rdx,4)
     +0x212: add     $0xfffffffffffffffc,%rcx
     +0x216: add     $0x8,%rdx
     +0x21a: cmp     $0xf8,%rdx
     +0x221: jb      <mldsa_poly_invntt_tomont+0x120>
     +0x227: lea     0x1c19e(%rip),%rcx
     +0x22e: mov     $0xfffffffffffffff0,%rdx
     +0x235: data16  cs nopw 0x0(%rax,%rax,1)
     +0x240: xor     %esi,%esi
     +0x242: sub     (%rcx),%esi
     +0x244: movslq  %esi,%rsi
     +0x247: mov     0x60(%rdi,%rdx,4),%r8d
     +0x24c: mov     0x40(%rdi,%rdx,4),%r9d
     +0x251: mov     0x44(%rdi,%rdx,4),%r10d
     +0x256: lea     (%r8,%r9,1),%r11d
     +0x25a: mov     %r11d,0x40(%rdi,%rdx,4)
     +0x25f: sub     %r8d,%r9d
     +0x262: movslq  %r9d,%r8
     +0x265: imul    %rsi,%r8
     +0x269: mov     %r8,%r9
     +0x26c: imul    %rax,%r9
     +0x270: sar     $0x20,%r9
     +0x274: imul    $0xffffffffff801fff,%r9,%r9
     +0x27b: add     %r8,%r9
     +0x27e: shr     $0x20,%r9
     +0x282: mov     %r9d,0x60(%rdi,%rdx,4)
     +0x287: mov     0x64(%rdi,%rdx,4),%r8d
     +0x28c: lea     (%r8,%r10,1),%r9d
     +0x290: mov     %r9d,0x44(%rdi,%rdx,4)
     +0x295: sub     %r8d,%r10d
     +0x298: movslq  %r10d,%r8
     +0x29b: imul    %rsi,%r8
     +0x29f: mov     %r8,%r9
     +0x2a2: imul    %rax,%r9
     +0x2a6: sar     $0x20,%r9
     +0x2aa: imul    $0xffffffffff801fff,%r9,%r9
     +0x2b1: add     %r8,%r9
     +0x2b4: shr     $0x20,%r9
     +0x2b8: mov     %r9d,0x64(%rdi,%rdx,4)
     +0x2bd: mov     0x48(%rdi,%rdx,4),%r8d
     +0x2c2: mov     0x68(%rdi,%rdx,4),%r9d
     +0x2c7: lea     (%r9,%r8,1),%r10d
     +0x2cb: mov     %r10d,0x48(%rdi,%rdx,4)
     +0x2d0: sub     %r9d,%r8d
     +0x2d3: movslq  %r8d,%r8
     +0x2d6: imul    %rsi,%r8
     +0x2da: mov     %r8,%r9
     +0x2dd: imul    %rax,%r9
     +0x2e1: sar     $0x20,%r9
     +0x2e5: imul    $0xffffffffff801fff,%r9,%r9
     +0x2ec: add     %r8,%r9
     +0x2ef: shr     $0x20,%r9
     +0x2f3: mov     %r9d,0x68(%rdi,%rdx,4)
     +0x2f8: mov     0x4c(%rdi,%rdx,4),%r8d
     +0x2fd: mov     0x6c(%rdi,%rdx,4),%r9d
     +0x302: lea     (%r9,%r8,1),%r10d
     +0x306: mov     %r10d,0x4c(%rdi,%rdx,4)
     +0x30b: sub     %r9d,%r8d
     +0x30e: movslq  %r8d,%r8
     +0x311: imul    %rsi,%r8
     +0x315: mov     %r8,%r9
     +0x318: imul    %rax,%r9
     +0x31c: sar     $0x20,%r9
     +0x320: imul    $0xffffffffff801fff,%r9,%r9
     +0x327: add     %r8,%r9
     +0x32a: shr     $0x20,%r9
     +0x32e: mov     %r9d,0x6c(%rdi,%rdx,4)
     +0x333: mov     0x50(%rdi,%rdx,4),%r8d
     +0x338: mov     0x70(%rdi,%rdx,4),%r9d
     +0x33d: lea     (%r9,%r8,1),%r10d
     +0x341: mov     %r10d,0x50(%rdi,%rdx,4)
     +0x346: sub     %r9d,%r8d
     +0x349: movslq  %r8d,%r8
     +0x34c: imul    %rsi,%r8
     +0x350: mov     %r8,%r9
     +0x353: imul    %rax,%r9
     +0x357: sar     $0x20,%r9
     +0x35b: imul    $0xffffffffff801fff,%r9,%r9
     +0x362: add     %r8,%r9
     +0x365: shr     $0x20,%r9
     +0x369: mov     %r9d,0x70(%rdi,%rdx,4)
     +0x36e: mov     0x54(%rdi,%rdx,4),%r8d
     +0x373: mov     0x74(%rdi,%rdx,4),%r9d
     +0x378: lea     (%r9,%r8,1),%r10d
     +0x37c: mov     %r10d,0x54(%rdi,%rdx,4)
     +0x381: sub     %r9d,%r8d
     +0x384: movslq  %r8d,%r8
     +0x387: imul    %rsi,%r8
     +0x38b: mov     %r8,%r9
     +0x38e: imul    %rax,%r9
     +0x392: sar     $0x20,%r9
     +0x396: imul    $0xffffffffff801fff,%r9,%r9
     +0x39d: add     %r8,%r9
     +0x3a0: shr     $0x20,%r9
     +0x3a4: mov     %r9d,0x74(%rdi,%rdx,4)
     +0x3a9: mov     0x58(%rdi,%rdx,4),%r8d
     +0x3ae: mov     0x78(%rdi,%rdx,4),%r9d
     +0x3b3: lea     (%r9,%r8,1),%r10d
     +0x3b7: mov     %r10d,0x58(%rdi,%rdx,4)
     +0x3bc: sub     %r9d,%r8d
     +0x3bf: movslq  %r8d,%r8
     +0x3c2: imul    %rsi,%r8
     +0x3c6: mov     %r8,%r9
     +0x3c9: imul    %rax,%r9
     +0x3cd: sar     $0x20,%r9
     +0x3d1: imul    $0xffffffffff801fff,%r9,%r9
     +0x3d8: add     %r8,%r9
     +0x3db: shr     $0x20,%r9
     +0x3df: mov     %r9d,0x78(%rdi,%rdx,4)
     +0x3e4: mov     0x5c(%rdi,%rdx,4),%r8d
     +0x3e9: mov     0x7c(%rdi,%rdx,4),%r9d
     +0x3ee: lea     (%r9,%r8,1),%r10d
     +0x3f2: mov     %r10d,0x5c(%rdi,%rdx,4)
     +0x3f7: sub     %r9d,%r8d
     +0x3fa: movslq  %r8d,%r8
     +0x3fd: imul    %rsi,%r8
     +0x401: mov     %r8,%rsi
     +0x404: imul    %rax,%rsi
     +0x408: sar     $0x20,%rsi
     +0x40c: imul    $0xffffffffff801fff,%rsi,%rsi
     +0x413: add     %r8,%rsi
     +0x416: shr     $0x20,%rsi
     +0x41a: mov     %esi,0x7c(%rdi,%rdx,4)
     +0x41e: add     $0xfffffffffffffffc,%rcx
     +0x422: add     $0x10,%rdx
     +0x426: cmp     $0xf0,%rdx
     +0x42d: jb      <mldsa_poly_invntt_tomont+0x240>
     +0x433: lea     0x7c(%rdi),%rcx
     +0x437: lea     0x1bf4e(%rip),%rdx
     +0x43e: mov     $0xffffffffffffffe0,%rsi
     +0x445: data16  cs nopw 0x0(%rax,%rax,1)
     +0x450: xor     %r8d,%r8d
     +0x453: sub     (%rdx),%r8d
     +0x456: movslq  %r8d,%r8
     +0x459: mov     0x44(%rcx,%rsi,4),%r9d
     +0x45e: mov     0x4(%rcx,%rsi,4),%r10d
     +0x463: mov     0x8(%rcx,%rsi,4),%r11d
     +0x468: lea     (%r9,%r10,1),%ebx
     +0x46c: mov     %ebx,0x4(%rcx,%rsi,4)
     +0x470: sub     %r9d,%r10d
     +0x473: movslq  %r10d,%r9
     +0x476: imul    %r8,%r9
     +0x47a: mov     %r9,%r10
     +0x47d: imul    %rax,%r10
     +0x481: sar     $0x20,%r10
     +0x485: imul    $0xffffffffff801fff,%r10,%r10
     +0x48c: add     %r9,%r10
     +0x48f: shr     $0x20,%r10
     +0x493: mov     %r10d,0x44(%rcx,%rsi,4)
     +0x498: mov     0x48(%rcx,%rsi,4),%r9d
     +0x49d: lea     (%r9,%r11,1),%r10d
     +0x4a1: mov     %r10d,0x8(%rcx,%rsi,4)
     +0x4a6: sub     %r9d,%r11d
     +0x4a9: movslq  %r11d,%r9
     +0x4ac: imul    %r8,%r9
     +0x4b0: mov     %r9,%r10
     +0x4b3: imul    %rax,%r10
     +0x4b7: sar     $0x20,%r10
     +0x4bb: imul    $0xffffffffff801fff,%r10,%r10
     +0x4c2: add     %r9,%r10
     +0x4c5: shr     $0x20,%r10
     +0x4c9: mov     %r10d,0x48(%rcx,%rsi,4)
     +0x4ce: mov     0xc(%rcx,%rsi,4),%r9d
     +0x4d3: mov     0x4c(%rcx,%rsi,4),%r10d
     +0x4d8: lea     (%r10,%r9,1),%r11d
     +0x4dc: mov     %r11d,0xc(%rcx,%rsi,4)
     +0x4e1: sub     %r10d,%r9d
     +0x4e4: movslq  %r9d,%r9
     +0x4e7: imul    %r8,%r9
     +0x4eb: mov     %r9,%r10
     +0x4ee: imul    %rax,%r10
     +0x4f2: sar     $0x20,%r10
     +0x4f6: imul    $0xffffffffff801fff,%r10,%r10
     +0x4fd: add     %r9,%r10
     +0x500: shr     $0x20,%r10
     +0x504: mov     %r10d,0x4c(%rcx,%rsi,4)
     +0x509: mov     0x10(%rcx,%rsi,4),%r9d
     +0x50e: mov     0x50(%rcx,%rsi,4),%r10d
     +0x513: lea     (%r10,%r9,1),%r11d
     +0x517: mov     %r11d,0x10(%rcx,%rsi,4)
     +0x51c: sub     %r10d,%r9d
     +0x51f: movslq  %r9d,%r9
     +0x522: imul    %r8,%r9
     +0x526: mov     %r9,%r10
     +0x529: imul    %rax,%r10
     +0x52d: sar     $0x20,%r10
     +0x531: imul    $0xffffffffff801fff,%r10,%r10
     +0x538: add     %r9,%r10
     +0x53b: shr     $0x20,%r10
     +0x53f: mov     %r10d,0x50(%rcx,%rsi,4)
     +0x544: mov     0x14(%rcx,%rsi,4),%r9d
     +0x549: mov     0x54(%rcx,%rsi,4),%r10d
     +0x54e: lea     (%r10,%r9,1),%r11d
     +0x552: mov     %r11d,0x14(%rcx,%rsi,4)
     +0x557: sub     %r10d,%r9d
     +0x55a: movslq  %r9d,%r9
     +0x55d: imul    %r8,%r9
     +0x561: mov     %r9,%r10
     +0x564: imul    %rax,%r10
     +0x568: sar     $0x20,%r10
     +0x56c: imul    $0xffffffffff801fff,%r10,%r10
     +0x573: add     %r9,%r10
     +0x576: shr     $0x20,%r10
     +0x57a: mov     %r10d,0x54(%rcx,%rsi,4)
     +0x57f: mov     0x18(%rcx,%rsi,4),%r9d
     +0x584: mov     0x58(%rcx,%rsi,4),%r10d
     +0x589: lea     (%r10,%r9,1),%r11d
     +0x58d: mov     %r11d,0x18(%rcx,%rsi,4)
     +0x592: sub     %r10d,%r9d
     +0x595: movslq  %r9d,%r9
     +0x598: imul    %r8,%r9
     +0x59c: mov     %r9,%r10
     +0x59f: imul    %rax,%r10
     +0x5a3: sar     $0x20,%r10
     +0x5a7: imul    $0xffffffffff801fff,%r10,%r10
     +0x5ae: add     %r9,%r10
     +0x5b1: shr     $0x20,%r10
     +0x5b5: mov     %r10d,0x58(%rcx,%rsi,4)
     +0x5ba: mov     0x1c(%rcx,%rsi,4),%r9d
     +0x5bf: mov     0x5c(%rcx,%rsi,4),%r10d
     +0x5c4: lea     (%r10,%r9,1),%r11d
     +0x5c8: mov     %r11d,0x1c(%rcx,%rsi,4)
     +0x5cd: sub     %r10d,%r9d
     +0x5d0: movslq  %r9d,%r9
     +0x5d3: imul    %r8,%r9
     +0x5d7: mov     %r9,%r10
     +0x5da: imul    %rax,%r10
     +0x5de: sar     $0x20,%r10
     +0x5e2: imul    $0xffffffffff801fff,%r10,%r10
     +0x5e9: add     %r9,%r10
     +0x5ec: shr     $0x20,%r10
     +0x5f0: mov     %r10d,0x5c(%rcx,%rsi,4)
     +0x5f5: mov     0x20(%rcx,%rsi,4),%r9d
     +0x5fa: mov     0x60(%rcx,%rsi,4),%r10d
     +0x5ff: lea     (%r10,%r9,1),%r11d
     +0x603: mov     %r11d,0x20(%rcx,%rsi,4)
     +0x608: sub     %r10d,%r9d
     +0x60b: movslq  %r9d,%r9
     +0x60e: imul    %r8,%r9
     +0x612: mov     %r9,%r10
     +0x615: imul    %rax,%r10
     +0x619: sar     $0x20,%r10
     +0x61d: imul    $0xffffffffff801fff,%r10,%r10
     +0x624: add     %r9,%r10
     +0x627: shr     $0x20,%r10
     +0x62b: mov     %r10d,0x60(%rcx,%rsi,4)
     +0x630: mov     0x24(%rcx,%rsi,4),%r9d
     +0x635: mov     0x64(%rcx,%rsi,4),%r10d
     +0x63a: lea     (%r10,%r9,1),%r11d
     +0x63e: mov     %r11d,0x24(%rcx,%rsi,4)
     +0x643: sub     %r10d,%r9d
     +0x646: movslq  %r9d,%r9
     +0x649: imul    %r8,%r9
     +0x64d: mov     %r9,%r10
     +0x650: imul    %rax,%r10
     +0x654: sar     $0x20,%r10
     +0x658: imul    $0xffffffffff801fff,%r10,%r10
     +0x65f: add     %r9,%r10
     +0x662: shr     $0x20,%r10
     +0x666: mov     %r10d,0x64(%rcx,%rsi,4)
     +0x66b: mov     0x28(%rcx,%rsi,4),%r9d
     +0x670: mov     0x68(%rcx,%rsi,4),%r10d
     +0x675: lea     (%r10,%r9,1),%r11d
     +0x679: mov     %r11d,0x28(%rcx,%rsi,4)
     +0x67e: sub     %r10d,%r9d
     +0x681: movslq  %r9d,%r9
     +0x684: imul    %r8,%r9
     +0x688: mov     %r9,%r10
     +0x68b: imul    %rax,%r10
     +0x68f: sar     $0x20,%r10
     +0x693: imul    $0xffffffffff801fff,%r10,%r10
     +0x69a: add     %r9,%r10
     +0x69d: shr     $0x20,%r10
     +0x6a1: mov     %r10d,0x68(%rcx,%rsi,4)
     +0x6a6: mov     0x2c(%rcx,%rsi,4),%r9d
     +0x6ab: mov     0x6c(%rcx,%rsi,4),%r10d
     +0x6b0: lea     (%r10,%r9,1),%r11d
     +0x6b4: mov     %r11d,0x2c(%rcx,%rsi,4)
     +0x6b9: sub     %r10d,%r9d
     +0x6bc: movslq  %r9d,%r9
     +0x6bf: imul    %r8,%r9
     +0x6c3: mov     %r9,%r10
     +0x6c6: imul    %rax,%r10
     +0x6ca: sar     $0x20,%r10
     +0x6ce: imul    $0xffffffffff801fff,%r10,%r10
     +0x6d5: add     %r9,%r10
     +0x6d8: shr     $0x20,%r10
     +0x6dc: mov     %r10d,0x6c(%rcx,%rsi,4)
     +0x6e1: mov     0x30(%rcx,%rsi,4),%r9d
     +0x6e6: mov     0x70(%rcx,%rsi,4),%r10d
     +0x6eb: lea     (%r10,%r9,1),%r11d
     +0x6ef: mov     %r11d,0x30(%rcx,%rsi,4)
     +0x6f4: sub     %r10d,%r9d
     +0x6f7: movslq  %r9d,%r9
     +0x6fa: imul    %r8,%r9
     +0x6fe: mov     %r9,%r10
     +0x701: imul    %rax,%r10
     +0x705: sar     $0x20,%r10
     +0x709: imul    $0xffffffffff801fff,%r10,%r10
     +0x710: add     %r9,%r10
     +0x713: shr     $0x20,%r10
     +0x717: mov     %r10d,0x70(%rcx,%rsi,4)
     +0x71c: mov     0x34(%rcx,%rsi,4),%r9d
     +0x721: mov     0x74(%rcx,%rsi,4),%r10d
     +0x726: lea     (%r10,%r9,1),%r11d
     +0x72a: mov     %r11d,0x34(%rcx,%rsi,4)
     +0x72f: sub     %r10d,%r9d
     +0x732: movslq  %r9d,%r9
     +0x735: imul    %r8,%r9
     +0x739: mov     %r9,%r10
     +0x73c: imul    %rax,%r10
     +0x740: sar     $0x20,%r10
     +0x744: imul    $0xffffffffff801fff,%r10,%r10
     +0x74b: add     %r9,%r10
     +0x74e: shr     $0x20,%r10
     +0x752: mov     %r10d,0x74(%rcx,%rsi,4)
     +0x757: mov     0x38(%rcx,%rsi,4),%r9d
     +0x75c: mov     0x78(%rcx,%rsi,4),%r10d
     +0x761: lea     (%r10,%r9,1),%r11d
     +0x765: mov     %r11d,0x38(%rcx,%rsi,4)
     +0x76a: sub     %r10d,%r9d
     +0x76d: movslq  %r9d,%r9
     +0x770: imul    %r8,%r9
     +0x774: mov     %r9,%r10
     +0x777: imul    %rax,%r10
     +0x77b: sar     $0x20,%r10
     +0x77f: imul    $0xffffffffff801fff,%r10,%r10
     +0x786: add     %r9,%r10
     +0x789: shr     $0x20,%r10
     +0x78d: mov     %r10d,0x78(%rcx,%rsi,4)
     +0x792: mov     0x3c(%rcx,%rsi,4),%r9d
     +0x797: mov     0x7c(%rcx,%rsi,4),%r10d
     +0x79c: lea     (%r10,%r9,1),%r11d
     +0x7a0: mov     %r11d,0x3c(%rcx,%rsi,4)
     +0x7a5: sub     %r10d,%r9d
     +0x7a8: movslq  %r9d,%r9
     +0x7ab: imul    %r8,%r9
     +0x7af: mov     %r9,%r10
     +0x7b2: imul    %rax,%r10
     +0x7b6: sar     $0x20,%r10
     +0x7ba: imul    $0xffffffffff801fff,%r10,%r10
     +0x7c1: add     %r9,%r10
     +0x7c4: shr     $0x20,%r10
     +0x7c8: mov     %r10d,0x7c(%rcx,%rsi,4)
     +0x7cd: mov     0x40(%rcx,%rsi,4),%r9d
     +0x7d2: mov     0x80(%rcx,%rsi,4),%r10d
     +0x7da: lea     (%r10,%r9,1),%r11d
     +0x7de: mov     %r11d,0x40(%rcx,%rsi,4)
     +0x7e3: sub     %r10d,%r9d
     +0x7e6: movslq  %r9d,%r9
     +0x7e9: imul    %r8,%r9
     +0x7ed: mov     %r9,%r8
     +0x7f0: imul    %rax,%r8
     +0x7f4: sar     $0x20,%r8
     +0x7f8: imul    $0xffffffffff801fff,%r8,%r8
     +0x7ff: add     %r9,%r8
     +0x802: shr     $0x20,%r8
     +0x806: mov     %r8d,0x80(%rcx,%rsi,4)
     +0x80e: add     $0xfffffffffffffffc,%rdx
     +0x812: add     $0x20,%rsi
     +0x816: cmp     $0xe0,%rsi
     +0x81d: jb      <mldsa_poly_invntt_tomont+0x450>
     +0x823: mov     $0xffffffffffffff80,%rax
     +0x82a: pxor    %xmm2,%xmm2
     +0x82e: movdqa  0x1b81a(%rip),%xmm3
     +0x836: movdqa  0x1b742(%rip),%xmm0
     +0x83e: movdqa  0x1b81a(%rip),%xmm4
     +0x846: movdqa  0x1b722(%rip),%xmm1
     +0x84e: xchg    %ax,%ax
     +0x850: movdqu  0x80(%rdi,%rax,1),%xmm5
     +0x859: movdqu  0x100(%rdi,%rax,1),%xmm6
     +0x862: movdqa  %xmm6,%xmm7
     +0x866: paddd   %xmm5,%xmm7
     +0x86a: movdqu  %xmm7,0x80(%rdi,%rax,1)
     +0x873: psubd   %xmm6,%xmm5
     +0x877: pxor    %xmm7,%xmm7
     +0x87b: pcmpgtd %xmm5,%xmm7
     +0x87f: pshufd  $0xee,%xmm5,%xmm6
     +0x884: punpckldq %xmm7,%xmm5
     +0x888: pxor    %xmm8,%xmm8
     +0x88d: pcmpgtd %xmm6,%xmm8
     +0x892: punpckldq %xmm8,%xmm6
     +0x897: movdqa  %xmm6,%xmm9
     +0x89c: pmuludq %xmm3,%xmm9
     +0x8a1: movdqa  %xmm6,%xmm10
     +0x8a6: pmuludq %xmm0,%xmm10
     +0x8ab: punpckldq %xmm2,%xmm8
     +0x8b0: pmuludq %xmm3,%xmm8
     +0x8b5: paddq   %xmm10,%xmm8
     +0x8ba: psllq   $0x20,%xmm8
     +0x8c0: paddq   %xmm9,%xmm8
     +0x8c5: movdqa  %xmm5,%xmm9
     +0x8ca: pmuludq %xmm3,%xmm9
     +0x8cf: movdqa  %xmm5,%xmm10
     +0x8d4: pmuludq %xmm0,%xmm10
     +0x8d9: punpckldq %xmm2,%xmm7
     +0x8dd: pmuludq %xmm3,%xmm7
     +0x8e1: paddq   %xmm10,%xmm7
     +0x8e6: psllq   $0x20,%xmm7
     +0x8eb: paddq   %xmm9,%xmm7
     +0x8f0: pmuludq %xmm4,%xmm6
     +0x8f4: pmuludq %xmm4,%xmm5
     +0x8f8: pshufd  $0xe8,%xmm5,%xmm9
     +0x8fe: psllq   $0x20,%xmm5
     +0x903: psrad   $0x1f,%xmm5
     +0x908: pshufd  $0xed,%xmm5,%xmm10
     +0x90e: punpckldq %xmm10,%xmm9
     +0x913: pshufd  $0xe8,%xmm6,%xmm10
     +0x919: psllq   $0x20,%xmm6
     +0x91e: psrad   $0x1f,%xmm6
     +0x923: pshufd  $0xed,%xmm6,%xmm11
     +0x929: punpckldq %xmm11,%xmm10
     +0x92e: movdqa  %xmm10,%xmm11
     +0x933: pmuludq %xmm1,%xmm11
     +0x938: paddq   %xmm8,%xmm11
     +0x93d: pmuludq %xmm0,%xmm10
     +0x942: psrlq   $0x20,%xmm6
     +0x947: pmuludq %xmm1,%xmm6
     +0x94b: paddq   %xmm10,%xmm6
     +0x950: psllq   $0x20,%xmm6
     +0x955: paddq   %xmm11,%xmm6
     +0x95a: movdqa  %xmm9,%xmm8
     +0x95f: pmuludq %xmm1,%xmm8
     +0x964: paddq   %xmm7,%xmm8
     +0x969: pmuludq %xmm0,%xmm9
     +0x96e: psrlq   $0x20,%xmm5
     +0x973: pmuludq %xmm1,%xmm5
     +0x977: paddq   %xmm9,%xmm5
     +0x97c: psllq   $0x20,%xmm5
     +0x981: paddq   %xmm8,%xmm5
     +0x986: shufps  $0xdd,%xmm6,%xmm5
     +0x98a: movups  %xmm5,0x100(%rdi,%rax,1)
     +0x992: add     $0x10,%rax
     +0x996: jne     <mldsa_poly_invntt_tomont+0x850>
     +0x99c: mov     $0xffffffffffffff80,%rax
     +0x9a3: pxor    %xmm2,%xmm2
     +0x9a7: movdqa  0x1b6c1(%rip),%xmm3
     +0x9af: movdqa  0x1b6c9(%rip),%xmm4
     +0x9b7: nopw    0x0(%rax,%rax,1)
     +0x9c0: movdqu  0x180(%rdi,%rax,1),%xmm5
     +0x9c9: movdqu  0x200(%rdi,%rax,1),%xmm6
     +0x9d2: movdqa  %xmm6,%xmm7
     +0x9d6: paddd   %xmm5,%xmm7
     +0x9da: movdqu  %xmm7,0x180(%rdi,%rax,1)
     +0x9e3: psubd   %xmm6,%xmm5
     +0x9e7: pxor    %xmm7,%xmm7
     +0x9eb: pcmpgtd %xmm5,%xmm7
     +0x9ef: pshufd  $0xee,%xmm5,%xmm6
     +0x9f4: punpckldq %xmm7,%xmm5
     +0x9f8: pxor    %xmm8,%xmm8
     +0x9fd: pcmpgtd %xmm6,%xmm8
     +0xa02: punpckldq %xmm8,%xmm6
     +0xa07: movdqa  %xmm6,%xmm9
     +0xa0c: pmuludq %xmm3,%xmm9
     +0xa11: punpckldq %xmm2,%xmm8
     +0xa16: pmuludq %xmm3,%xmm8
     +0xa1b: psllq   $0x20,%xmm8
     +0xa21: paddq   %xmm9,%xmm8
     +0xa26: movdqa  %xmm5,%xmm9
     +0xa2b: pmuludq %xmm3,%xmm9
     +0xa30: punpckldq %xmm2,%xmm7
     +0xa34: pmuludq %xmm3,%xmm7
     +0xa38: psllq   $0x20,%xmm7
     +0xa3d: paddq   %xmm9,%xmm7
     +0xa42: pmuludq %xmm4,%xmm6
     +0xa46: pmuludq %xmm4,%xmm5
     +0xa4a: pshufd  $0xe8,%xmm5,%xmm9
     +0xa50: psllq   $0x20,%xmm5
     +0xa55: psrad   $0x1f,%xmm5
     +0xa5a: pshufd  $0xed,%xmm5,%xmm10
     +0xa60: punpckldq %xmm10,%xmm9
     +0xa65: pshufd  $0xe8,%xmm6,%xmm10
     +0xa6b: psllq   $0x20,%xmm6
     +0xa70: psrad   $0x1f,%xmm6
     +0xa75: pshufd  $0xed,%xmm6,%xmm11
     +0xa7b: punpckldq %xmm11,%xmm10
     +0xa80: movdqa  %xmm10,%xmm11
     +0xa85: pmuludq %xmm1,%xmm11
     +0xa8a: paddq   %xmm8,%xmm11
     +0xa8f: pmuludq %xmm0,%xmm10
     +0xa94: psrlq   $0x20,%xmm6
     +0xa99: pmuludq %xmm1,%xmm6
     +0xa9d: paddq   %xmm10,%xmm6
     +0xaa2: psllq   $0x20,%xmm6
     +0xaa7: paddq   %xmm11,%xmm6
     +0xaac: movdqa  %xmm9,%xmm8
     +0xab1: pmuludq %xmm1,%xmm8
     +0xab6: paddq   %xmm7,%xmm8
     +0xabb: pmuludq %xmm0,%xmm9
     +0xac0: psrlq   $0x20,%xmm5
     +0xac5: pmuludq %xmm1,%xmm5
     +0xac9: paddq   %xmm9,%xmm5
     +0xace: psllq   $0x20,%xmm5
     +0xad3: paddq   %xmm8,%xmm5
     +0xad8: shufps  $0xdd,%xmm6,%xmm5
     +0xadc: movups  %xmm5,0x200(%rdi,%rax,1)
     +0xae4: add     $0x10,%rax
     +0xae8: jne     <mldsa_poly_invntt_tomont+0x9c0>
     +0xaee: mov     $0xffffffffffffff80,%rax
     +0xaf5: pxor    %xmm2,%xmm2
     +0xaf9: movdqa  0x1b58f(%rip),%xmm3
     +0xb01: movdqa  0x1b597(%rip),%xmm4
     +0xb09: nopl    0x0(%rax)
     +0xb10: movdqu  0x280(%rdi,%rax,1),%xmm5
     +0xb19: movdqu  0x300(%rdi,%rax,1),%xmm6
     +0xb22: movdqa  %xmm6,%xmm7
     +0xb26: paddd   %xmm5,%xmm7
     +0xb2a: movdqu  %xmm7,0x280(%rdi,%rax,1)
     +0xb33: psubd   %xmm6,%xmm5
     +0xb37: pxor    %xmm7,%xmm7
     +0xb3b: pcmpgtd %xmm5,%xmm7
     +0xb3f: pshufd  $0xee,%xmm5,%xmm6
     +0xb44: punpckldq %xmm7,%xmm5
     +0xb48: pxor    %xmm8,%xmm8
     +0xb4d: pcmpgtd %xmm6,%xmm8
     +0xb52: punpckldq %xmm8,%xmm6
     +0xb57: movdqa  %xmm6,%xmm9
     +0xb5c: pmuludq %xmm3,%xmm9
     +0xb61: punpckldq %xmm2,%xmm8
     +0xb66: pmuludq %xmm3,%xmm8
     +0xb6b: psllq   $0x20,%xmm8
     +0xb71: paddq   %xmm9,%xmm8
     +0xb76: movdqa  %xmm5,%xmm9
     +0xb7b: pmuludq %xmm3,%xmm9
     +0xb80: punpckldq %xmm2,%xmm7
     +0xb84: pmuludq %xmm3,%xmm7
     +0xb88: psllq   $0x20,%xmm7
     +0xb8d: paddq   %xmm9,%xmm7
     +0xb92: pmuludq %xmm4,%xmm6
     +0xb96: pmuludq %xmm4,%xmm5
     +0xb9a: pshufd  $0xe8,%xmm5,%xmm9
     +0xba0: psllq   $0x20,%xmm5
     +0xba5: psrad   $0x1f,%xmm5
     +0xbaa: pshufd  $0xed,%xmm5,%xmm10
     +0xbb0: punpckldq %xmm10,%xmm9
     +0xbb5: pshufd  $0xe8,%xmm6,%xmm10
     +0xbbb: psllq   $0x20,%xmm6
     +0xbc0: psrad   $0x1f,%xmm6
     +0xbc5: pshufd  $0xed,%xmm6,%xmm11
     +0xbcb: punpckldq %xmm11,%xmm10
     +0xbd0: movdqa  %xmm10,%xmm11
     +0xbd5: pmuludq %xmm1,%xmm11
     +0xbda: paddq   %xmm8,%xmm11
     +0xbdf: pmuludq %xmm0,%xmm10
     +0xbe4: psrlq   $0x20,%xmm6
     +0xbe9: pmuludq %xmm1,%xmm6
     +0xbed: paddq   %xmm10,%xmm6
     +0xbf2: psllq   $0x20,%xmm6
     +0xbf7: paddq   %xmm11,%xmm6
     +0xbfc: movdqa  %xmm9,%xmm8
     +0xc01: pmuludq %xmm1,%xmm8
     +0xc06: paddq   %xmm7,%xmm8
     +0xc0b: pmuludq %xmm0,%xmm9
     +0xc10: psrlq   $0x20,%xmm5
     +0xc15: pmuludq %xmm1,%xmm5
     +0xc19: paddq   %xmm9,%xmm5
     +0xc1e: psllq   $0x20,%xmm5
     +0xc23: paddq   %xmm8,%xmm5
     +0xc28: shufps  $0xdd,%xmm6,%xmm5
     +0xc2c: movups  %xmm5,0x300(%rdi,%rax,1)
     +0xc34: add     $0x10,%rax
     +0xc38: jne     <mldsa_poly_invntt_tomont+0xb10>
     +0xc3e: mov     $0xffffffffffffff80,%rax
     +0xc45: pxor    %xmm2,%xmm2
     +0xc49: movdqa  0x1b45f(%rip),%xmm3
     +0xc51: movdqa  0x1b467(%rip),%xmm4
     +0xc59: nopl    0x0(%rax)
     +0xc60: movdqu  0x380(%rdi,%rax,1),%xmm5
     +0xc69: movdqu  0x400(%rdi,%rax,1),%xmm6
     +0xc72: movdqa  %xmm6,%xmm7
     +0xc76: paddd   %xmm5,%xmm7
     +0xc7a: movdqu  %xmm7,0x380(%rdi,%rax,1)
     +0xc83: psubd   %xmm6,%xmm5
     +0xc87: pxor    %xmm7,%xmm7
     +0xc8b: pcmpgtd %xmm5,%xmm7
     +0xc8f: pshufd  $0xee,%xmm5,%xmm6
     +0xc94: punpckldq %xmm7,%xmm5
     +0xc98: pxor    %xmm8,%xmm8
     +0xc9d: pcmpgtd %xmm6,%xmm8
     +0xca2: punpckldq %xmm8,%xmm6
     +0xca7: movdqa  %xmm6,%xmm9
     +0xcac: pmuludq %xmm3,%xmm9
     +0xcb1: movdqa  %xmm6,%xmm10
     +0xcb6: pmuludq %xmm0,%xmm10
     +0xcbb: punpckldq %xmm2,%xmm8
     +0xcc0: pmuludq %xmm3,%xmm8
     +0xcc5: paddq   %xmm10,%xmm8
     +0xcca: psllq   $0x20,%xmm8
     +0xcd0: paddq   %xmm9,%xmm8
     +0xcd5: movdqa  %xmm5,%xmm9
     +0xcda: pmuludq %xmm3,%xmm9
     +0xcdf: movdqa  %xmm5,%xmm10
     +0xce4: pmuludq %xmm0,%xmm10
     +0xce9: punpckldq %xmm2,%xmm7
     +0xced: pmuludq %xmm3,%xmm7
     +0xcf1: paddq   %xmm10,%xmm7
     +0xcf6: psllq   $0x20,%xmm7
     +0xcfb: paddq   %xmm9,%xmm7
     +0xd00: pmuludq %xmm4,%xmm6
     +0xd04: pmuludq %xmm4,%xmm5
     +0xd08: pshufd  $0xe8,%xmm5,%xmm9
     +0xd0e: psllq   $0x20,%xmm5
     +0xd13: psrad   $0x1f,%xmm5
     +0xd18: pshufd  $0xed,%xmm5,%xmm10
     +0xd1e: punpckldq %xmm10,%xmm9
     +0xd23: pshufd  $0xe8,%xmm6,%xmm10
     +0xd29: psllq   $0x20,%xmm6
     +0xd2e: psrad   $0x1f,%xmm6
     +0xd33: pshufd  $0xed,%xmm6,%xmm11
     +0xd39: punpckldq %xmm11,%xmm10
     +0xd3e: movdqa  %xmm10,%xmm11
     +0xd43: pmuludq %xmm1,%xmm11
     +0xd48: paddq   %xmm8,%xmm11
     +0xd4d: pmuludq %xmm0,%xmm10
     +0xd52: psrlq   $0x20,%xmm6
     +0xd57: pmuludq %xmm1,%xmm6
     +0xd5b: paddq   %xmm10,%xmm6
     +0xd60: psllq   $0x20,%xmm6
     +0xd65: paddq   %xmm11,%xmm6
     +0xd6a: movdqa  %xmm9,%xmm8
     +0xd6f: pmuludq %xmm1,%xmm8
     +0xd74: paddq   %xmm7,%xmm8
     +0xd79: pmuludq %xmm0,%xmm9
     +0xd7e: psrlq   $0x20,%xmm5
     +0xd83: pmuludq %xmm1,%xmm5
     +0xd87: paddq   %xmm9,%xmm5
     +0xd8c: psllq   $0x20,%xmm5
     +0xd91: paddq   %xmm8,%xmm5
     +0xd96: shufps  $0xdd,%xmm6,%xmm5
     +0xd9a: movups  %xmm5,0x400(%rdi,%rax,1)
     +0xda2: add     $0x10,%rax
     +0xda6: jne     <mldsa_poly_invntt_tomont+0xc60>
     +0xdac: mov     $0xffffffffffffff00,%rax
     +0xdb3: pxor    %xmm2,%xmm2
     +0xdb7: movdqa  0x1b311(%rip),%xmm3
     +0xdbf: movdqa  0x1b319(%rip),%xmm4
     +0xdc7: nopw    0x0(%rax,%rax,1)
     +0xdd0: movdqu  0x100(%rdi,%rax,1),%xmm5
     +0xdd9: movdqu  0x200(%rdi,%rax,1),%xmm6
     +0xde2: movdqa  %xmm6,%xmm7
     +0xde6: paddd   %xmm5,%xmm7
     +0xdea: movdqu  %xmm7,0x100(%rdi,%rax,1)
     +0xdf3: psubd   %xmm6,%xmm5
     +0xdf7: pxor    %xmm7,%xmm7
     +0xdfb: pcmpgtd %xmm5,%xmm7
     +0xdff: pshufd  $0xee,%xmm5,%xmm6
     +0xe04: punpckldq %xmm7,%xmm5
     +0xe08: pxor    %xmm8,%xmm8
     +0xe0d: pcmpgtd %xmm6,%xmm8
     +0xe12: punpckldq %xmm8,%xmm6
     +0xe17: movdqa  %xmm6,%xmm9
     +0xe1c: pmuludq %xmm3,%xmm9
     +0xe21: punpckldq %xmm2,%xmm8
     +0xe26: pmuludq %xmm3,%xmm8
     +0xe2b: psllq   $0x20,%xmm8
     +0xe31: paddq   %xmm9,%xmm8
     +0xe36: movdqa  %xmm5,%xmm9
     +0xe3b: pmuludq %xmm3,%xmm9
     +0xe40: punpckldq %xmm2,%xmm7
     +0xe44: pmuludq %xmm3,%xmm7
     +0xe48: psllq   $0x20,%xmm7
     +0xe4d: paddq   %xmm9,%xmm7
     +0xe52: pmuludq %xmm4,%xmm6
     +0xe56: pmuludq %xmm4,%xmm5
     +0xe5a: pshufd  $0xe8,%xmm5,%xmm9
     +0xe60: psllq   $0x20,%xmm5
     +0xe65: psrad   $0x1f,%xmm5
     +0xe6a: pshufd  $0xed,%xmm5,%xmm10
     +0xe70: punpckldq %xmm10,%xmm9
     +0xe75: pshufd  $0xe8,%xmm6,%xmm10
     +0xe7b: psllq   $0x20,%xmm6
     +0xe80: psrad   $0x1f,%xmm6
     +0xe85: pshufd  $0xed,%xmm6,%xmm11
     +0xe8b: punpckldq %xmm11,%xmm10
     +0xe90: movdqa  %xmm10,%xmm11
     +0xe95: pmuludq %xmm1,%xmm11
     +0xe9a: paddq   %xmm8,%xmm11
     +0xe9f: pmuludq %xmm0,%xmm10
     +0xea4: psrlq   $0x20,%xmm6
     +0xea9: pmuludq %xmm1,%xmm6
     +0xead: paddq   %xmm10,%xmm6
     +0xeb2: psllq   $0x20,%xmm6
     +0xeb7: paddq   %xmm11,%xmm6
     +0xebc: movdqa  %xmm9,%xmm8
     +0xec1: pmuludq %xmm1,%xmm8
     +0xec6: paddq   %xmm7,%xmm8
     +0xecb: pmuludq %xmm0,%xmm9
     +0xed0: psrlq   $0x20,%xmm5
     +0xed5: pmuludq %xmm1,%xmm5
     +0xed9: paddq   %xmm9,%xmm5
     +0xede: psllq   $0x20,%xmm5
     +0xee3: paddq   %xmm8,%xmm5
     +0xee8: shufps  $0xdd,%xmm6,%xmm5
     +0xeec: movups  %xmm5,0x200(%rdi,%rax,1)
     +0xef4: add     $0x10,%rax
     +0xef8: jne     <mldsa_poly_invntt_tomont+0xdd0>
     +0xefe: mov     $0xffffffffffffff00,%rax
     +0xf05: pxor    %xmm2,%xmm2
     +0xf09: movdqa  0x1b1df(%rip),%xmm3
     +0xf11: movdqa  0x1b1e7(%rip),%xmm4
     +0xf19: nopl    0x0(%rax)
     +0xf20: movdqu  0x300(%rdi,%rax,1),%xmm5
     +0xf29: movdqu  0x400(%rdi,%rax,1),%xmm6
     +0xf32: movdqa  %xmm6,%xmm7
     +0xf36: paddd   %xmm5,%xmm7
     +0xf3a: movdqu  %xmm7,0x300(%rdi,%rax,1)
     +0xf43: psubd   %xmm6,%xmm5
     +0xf47: pxor    %xmm7,%xmm7
     +0xf4b: pcmpgtd %xmm5,%xmm7
     +0xf4f: pshufd  $0xee,%xmm5,%xmm6
     +0xf54: punpckldq %xmm7,%xmm5
     +0xf58: pxor    %xmm8,%xmm8
     +0xf5d: pcmpgtd %xmm6,%xmm8
     +0xf62: punpckldq %xmm8,%xmm6
     +0xf67: movdqa  %xmm6,%xmm9
     +0xf6c: pmuludq %xmm3,%xmm9
     +0xf71: punpckldq %xmm2,%xmm8
     +0xf76: pmuludq %xmm3,%xmm8
     +0xf7b: psllq   $0x20,%xmm8
     +0xf81: paddq   %xmm9,%xmm8
     +0xf86: movdqa  %xmm5,%xmm9
     +0xf8b: pmuludq %xmm3,%xmm9
     +0xf90: punpckldq %xmm2,%xmm7
     +0xf94: pmuludq %xmm3,%xmm7
     +0xf98: psllq   $0x20,%xmm7
     +0xf9d: paddq   %xmm9,%xmm7
     +0xfa2: pmuludq %xmm4,%xmm6
     +0xfa6: pmuludq %xmm4,%xmm5
     +0xfaa: pshufd  $0xe8,%xmm5,%xmm9
     +0xfb0: psllq   $0x20,%xmm5
     +0xfb5: psrad   $0x1f,%xmm5
     +0xfba: pshufd  $0xed,%xmm5,%xmm10
     +0xfc0: punpckldq %xmm10,%xmm9
     +0xfc5: pshufd  $0xe8,%xmm6,%xmm10
     +0xfcb: psllq   $0x20,%xmm6
     +0xfd0: psrad   $0x1f,%xmm6
     +0xfd5: pshufd  $0xed,%xmm6,%xmm11
     +0xfdb: punpckldq %xmm11,%xmm10
     +0xfe0: movdqa  %xmm10,%xmm11
     +0xfe5: pmuludq %xmm1,%xmm11
     +0xfea: paddq   %xmm8,%xmm11
     +0xfef: pmuludq %xmm0,%xmm10
     +0xff4: psrlq   $0x20,%xmm6
     +0xff9: pmuludq %xmm1,%xmm6
     +0xffd: paddq   %xmm10,%xmm6
    +0x1002: psllq   $0x20,%xmm6
    +0x1007: paddq   %xmm11,%xmm6
    +0x100c: movdqa  %xmm9,%xmm8
    +0x1011: pmuludq %xmm1,%xmm8
    +0x1016: paddq   %xmm7,%xmm8
    +0x101b: pmuludq %xmm0,%xmm9
    +0x1020: psrlq   $0x20,%xmm5
    +0x1025: pmuludq %xmm1,%xmm5
    +0x1029: paddq   %xmm9,%xmm5
    +0x102e: psllq   $0x20,%xmm5
    +0x1033: paddq   %xmm8,%xmm5
    +0x1038: shufps  $0xdd,%xmm6,%xmm5
    +0x103c: movups  %xmm5,0x400(%rdi,%rax,1)
    +0x1044: add     $0x10,%rax
    +0x1048: jne     <mldsa_poly_invntt_tomont+0xf20>
    +0x104e: mov     $0xfffffffffffffe00,%rax
    +0x1055: pxor    %xmm2,%xmm2
    +0x1059: movdqa  0x1b0af(%rip),%xmm3
    +0x1061: movdqa  0x1b0b7(%rip),%xmm4
    +0x1069: nopl    0x0(%rax)
    +0x1070: movdqu  0x200(%rdi,%rax,1),%xmm5
    +0x1079: movdqu  0x400(%rdi,%rax,1),%xmm6
    +0x1082: movdqa  %xmm6,%xmm7
    +0x1086: paddd   %xmm5,%xmm7
    +0x108a: movdqu  %xmm7,0x200(%rdi,%rax,1)
    +0x1093: psubd   %xmm6,%xmm5
    +0x1097: pxor    %xmm7,%xmm7
    +0x109b: pcmpgtd %xmm5,%xmm7
    +0x109f: pshufd  $0xee,%xmm5,%xmm6
    +0x10a4: punpckldq %xmm7,%xmm5
    +0x10a8: pxor    %xmm8,%xmm8
    +0x10ad: pcmpgtd %xmm6,%xmm8
    +0x10b2: punpckldq %xmm8,%xmm6
    +0x10b7: movdqa  %xmm6,%xmm9
    +0x10bc: pmuludq %xmm3,%xmm9
    +0x10c1: movdqa  %xmm6,%xmm10
    +0x10c6: pmuludq %xmm0,%xmm10
    +0x10cb: punpckldq %xmm2,%xmm8
    +0x10d0: pmuludq %xmm3,%xmm8
    +0x10d5: paddq   %xmm10,%xmm8
    +0x10da: psllq   $0x20,%xmm8
    +0x10e0: paddq   %xmm9,%xmm8
    +0x10e5: movdqa  %xmm5,%xmm9
    +0x10ea: pmuludq %xmm3,%xmm9
    +0x10ef: movdqa  %xmm5,%xmm10
    +0x10f4: pmuludq %xmm0,%xmm10
    +0x10f9: punpckldq %xmm2,%xmm7
    +0x10fd: pmuludq %xmm3,%xmm7
    +0x1101: paddq   %xmm10,%xmm7
    +0x1106: psllq   $0x20,%xmm7
    +0x110b: paddq   %xmm9,%xmm7
    +0x1110: pmuludq %xmm4,%xmm6
    +0x1114: pmuludq %xmm4,%xmm5
    +0x1118: pshufd  $0xe8,%xmm5,%xmm9
    +0x111e: psllq   $0x20,%xmm5
    +0x1123: psrad   $0x1f,%xmm5
    +0x1128: pshufd  $0xed,%xmm5,%xmm10
    +0x112e: punpckldq %xmm10,%xmm9
    +0x1133: pshufd  $0xe8,%xmm6,%xmm10
    +0x1139: psllq   $0x20,%xmm6
    +0x113e: psrad   $0x1f,%xmm6
    +0x1143: pshufd  $0xed,%xmm6,%xmm11
    +0x1149: punpckldq %xmm11,%xmm10
    +0x114e: movdqa  %xmm10,%xmm11
    +0x1153: pmuludq %xmm1,%xmm11
    +0x1158: paddq   %xmm8,%xmm11
    +0x115d: pmuludq %xmm0,%xmm10
    +0x1162: psrlq   $0x20,%xmm6
    +0x1167: pmuludq %xmm1,%xmm6
    +0x116b: paddq   %xmm10,%xmm6
    +0x1170: psllq   $0x20,%xmm6
    +0x1175: paddq   %xmm11,%xmm6
    +0x117a: movdqa  %xmm9,%xmm8
    +0x117f: pmuludq %xmm1,%xmm8
    +0x1184: paddq   %xmm7,%xmm8
    +0x1189: pmuludq %xmm0,%xmm9
    +0x118e: psrlq   $0x20,%xmm5
    +0x1193: pmuludq %xmm1,%xmm5
    +0x1197: paddq   %xmm9,%xmm5
    +0x119c: psllq   $0x20,%xmm5
    +0x11a1: paddq   %xmm8,%xmm5
    +0x11a6: shufps  $0xdd,%xmm6,%xmm5
    +0x11aa: movups  %xmm5,0x400(%rdi,%rax,1)
    +0x11b2: add     $0x10,%rax
    +0x11b6: jne     <mldsa_poly_invntt_tomont+0x1070>
    +0x11bc: movabs  $0xff7fe3fa00000000,%rax
    +0x11c6: xor     %ecx,%ecx
    +0x11c8: nopl    0x0(%rax,%rax,1)
    +0x11d0: movslq  (%rdi,%rcx,4),%rdx
    +0x11d4: imul    $0xa3fa,%rdx,%rsi
    +0x11db: imul    %rax,%rdx
    +0x11df: sar     $0x20,%rdx
    +0x11e3: imul    $0xffffffffff801fff,%rdx,%rdx
    +0x11ea: add     %rsi,%rdx
    +0x11ed: shr     $0x20,%rdx
    +0x11f1: mov     %edx,(%rdi,%rcx,4)
    +0x11f4: movslq  0x4(%rdi,%rcx,4),%rdx
    +0x11f9: imul    $0xa3fa,%rdx,%rsi
    +0x1200: imul    %rax,%rdx
    +0x1204: sar     $0x20,%rdx
    +0x1208: imul    $0xffffffffff801fff,%rdx,%rdx
    +0x120f: add     %rsi,%rdx
    +0x1212: shr     $0x20,%rdx
    +0x1216: mov     %edx,0x4(%rdi,%rcx,4)
    +0x121a: add     $0x2,%rcx
    +0x121e: cmp     $0x100,%rcx
    +0x1225: jne     <mldsa_poly_invntt_tomont+0x11d0>
    +0x1227: pop     %rbx
    +0x1228: xor     %eax,%eax
    +0x122a: xor     %ecx,%ecx
    +0x122c: xor     %edi,%edi
    +0x122e: xor     %edx,%edx
    +0x1230: xor     %esi,%esi
    +0x1232: xor     %r8d,%r8d
    +0x1235: xor     %r9d,%r9d
    +0x1238: xor     %r10d,%r10d
    +0x123b: xor     %r11d,%r11d
    +0x123e: ret     
 ***)

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa_poly_invntt_tomont"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The polynomial x at a, 256 coefficients of 32 bits each,     *)
(* becomes mld_poly_invntt_tomont x. The function saves RBX, RBP and R12-R15 *)
(* below the return address and keeps a temporary in the 8 bytes below them  *)
(* (the red zone), the stack frame of 56 bytes.                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (a,1024))
            [(word_sub stackpointer (word 8),8); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(a,1024); (word_sub stackpointer (word 8),8)]
         [(word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa_poly_invntt_tomont) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add a (word(4 * i))))
                            s = mld_poly_invntt_tomont x i)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(a,1024);
                memory :> bytes(word_sub stackpointer (word 8),8)])`;;

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* polynomial, the table of zetas in the image, the stack frame and the slot *)
(* of the return address, and the writes within the polynomial and the stack *)
(* frame.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (a,1024))
            [(word_sub stackpointer (word 8),8); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(a,1024); (word_sub stackpointer (word 8),8)]
         [(word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa_poly_invntt_tomont) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = mld_poly_invntt_tomont x i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a pc (word_sub stackpointer (word 8))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [a,1024; word(pc + rodata_mld_zetas),1024;
                       word(pc + mldsa_poly_invntt_tomont_consts),448;
                       word_sub stackpointer (word 8),8; stackpointer,8]
                      [a,1024; word_sub stackpointer (word 8),8]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(a,1024);
                memory :> bytes(word_sub stackpointer (word 8),8)])`;;

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e a pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (a,1024))
            [(word_sub stackpointer (word 8),8); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(a,1024); (word_sub stackpointer (word 8),8)]
         [(word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa_poly_invntt_tomont) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a pc (word_sub stackpointer (word 8))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [a,1024; word(pc + rodata_mld_zetas),1024;
                       word(pc + mldsa_poly_invntt_tomont_consts),448;
                       word_sub stackpointer (word 8),8; stackpointer,8]
                      [a,1024; word_sub stackpointer (word 8),8]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(a,1024);
                memory :> bytes(word_sub stackpointer (word 8),8)])`;;

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
