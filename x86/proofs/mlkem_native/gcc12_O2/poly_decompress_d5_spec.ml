(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of a polynomial from 5 bits per coefficient. This is the    *)
(* code for mlkem_poly_decompress_d5 from mlkem-native's portable C          *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md).  *)
(* It is verified in the whole image (see libmlkem.ml). The constant vector  *)
(* of 16s that it uses for the rounding is in the image. It saves three      *)
(* registers on the stack, so it is verified directly as a subroutine, with  *)
(* that part of the stack.                                                   *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mlkem_native.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_decompress_d5:
       +0x0: push   r12
       +0x2: mov    rdx,rsi
       +0x5: mov    rcx,rdi
       +0x8: lea    rsi,[rsi+0xa0]
       +0xf: push   rbp
      +0x10: pxor   xmm4,xmm4
      +0x14: pxor   xmm2,xmm2
      +0x18: movq   xmm3,QWORD PTR [rip+0x5220]
      +0x20: push   rbx
      +0x21: nop    DWORD PTR [rax+0x0]
      +0x28: movzx  edi,BYTE PTR [rdx]
      +0x2b: movzx  r10d,BYTE PTR [rdx+0x1]
      +0x30: movzx  r11d,BYTE PTR [rdx+0x2]
      +0x35: movzx  ebx,BYTE PTR [rdx+0x3]
      +0x39: mov    r9d,edi
      +0x3c: lea    r8d,[r10*8+0x0]
      +0x44: movzx  eax,BYTE PTR [rdx+0x4]
      +0x48: and    edi,0x1f
      +0x4b: shr    r9b,0x5
      +0x4f: lea    ebp,[r11+r11*1]
      +0x53: shr    r11b,0x4
      +0x57: or     r8d,r9d
      +0x5a: mov    r9d,r10d
      +0x5d: shr    r10b,0x7
      +0x61: lea    r12d,[rax*4+0x0]
      +0x69: shr    al,0x3
      +0x6c: or     r10d,ebp
      +0x6f: mov    ebp,ebx
      +0x71: shr    r9b,0x2
      +0x75: shl    ebp,0x4
      +0x78: movzx  eax,al
      +0x7b: and    r10d,0x1f
      +0x7f: and    r9d,0x1f
      +0x83: or     r11d,ebp
      +0x86: mov    ebp,ebx
      +0x88: shr    bl,0x6
      +0x8b: and    r8d,0x1f
      +0x8f: shl    rax,0x8
      +0x93: or     ebx,r12d
      +0x96: shr    bpl,1
      +0x99: and    r11d,0x1f
      +0x9d: and    ebx,0x1f
      +0xa0: and    ebp,0x1f
      +0xa3: or     rax,rbx
      +0xa6: shl    rax,0x8
      +0xaa: or     rax,rbp
      +0xad: shl    rax,0x8
      +0xb1: or     rax,r11
      +0xb4: shl    rax,0x8
      +0xb8: or     rax,r10
      +0xbb: shl    rax,0x8
      +0xbf: or     rax,r9
      +0xc2: shl    rax,0x8
      +0xc6: or     rax,r8
      +0xc9: shl    rax,0x8
      +0xcd: or     rax,rdi
      +0xd0: add    rdx,0x5
      +0xd4: add    rcx,0x10
      +0xd8: movq   xmm0,rax
      +0xdd: movdqa xmm6,xmm0
      +0xe1: punpcklbw xmm0,xmm4
      +0xe5: punpcklbw xmm6,xmm4
      +0xe9: pshufd xmm0,xmm0,0x4e
      +0xee: movdqa xmm5,xmm6
      +0xf2: punpcklwd xmm6,xmm2
      +0xf6: movdqa xmm7,xmm0
      +0xfa: punpcklwd xmm5,xmm2
      +0xfe: pshufd xmm6,xmm6,0x4e
     +0x103: punpcklwd xmm7,xmm2
     +0x107: movdqa xmm1,xmm5
     +0x10b: punpcklwd xmm0,xmm2
     +0x10f: pslld  xmm1,0x1
     +0x114: pshufd xmm0,xmm0,0x4e
     +0x119: paddd  xmm1,xmm5
     +0x11d: pslld  xmm1,0x2
     +0x122: paddd  xmm1,xmm5
     +0x126: paddd  xmm5,xmm3
     +0x12a: pslld  xmm1,0x8
     +0x12f: paddd  xmm1,xmm5
     +0x133: movdqa xmm5,xmm6
     +0x137: pslld  xmm5,0x1
     +0x13c: paddd  xmm5,xmm6
     +0x140: psrld  xmm1,0x5
     +0x145: pslld  xmm5,0x2
     +0x14a: paddd  xmm5,xmm6
     +0x14e: paddd  xmm6,xmm3
     +0x152: pslld  xmm5,0x8
     +0x157: paddd  xmm5,xmm6
     +0x15b: movdqa xmm6,xmm1
     +0x15f: psrld  xmm5,0x5
     +0x164: punpcklwd xmm6,xmm5
     +0x168: punpcklwd xmm1,xmm5
     +0x16c: movdqa xmm5,xmm0
     +0x170: pshufd xmm6,xmm6,0x4e
     +0x175: pslld  xmm5,0x1
     +0x17a: punpcklwd xmm1,xmm6
     +0x17e: paddd  xmm5,xmm0
     +0x182: movq   QWORD PTR [rcx-0x10],xmm1
     +0x187: movdqa xmm1,xmm7
     +0x18b: pslld  xmm1,0x1
     +0x190: paddd  xmm1,xmm7
     +0x194: pslld  xmm5,0x2
     +0x199: paddd  xmm5,xmm0
     +0x19d: paddd  xmm0,xmm3
     +0x1a1: pslld  xmm1,0x2
     +0x1a6: paddd  xmm1,xmm7
     +0x1aa: paddd  xmm7,xmm3
     +0x1ae: pslld  xmm5,0x8
     +0x1b3: paddd  xmm0,xmm5
     +0x1b7: pslld  xmm1,0x8
     +0x1bc: paddd  xmm1,xmm7
     +0x1c0: psrld  xmm0,0x5
     +0x1c5: psrld  xmm1,0x5
     +0x1ca: movdqa xmm5,xmm1
     +0x1ce: punpcklwd xmm1,xmm0
     +0x1d2: punpcklwd xmm5,xmm0
     +0x1d6: pshufd xmm5,xmm5,0x4e
     +0x1db: punpcklwd xmm1,xmm5
     +0x1df: movq   QWORD PTR [rcx-0x8],xmm1
     +0x1e4: cmp    rdx,rsi
     +0x1e7: jne    <mlkem_poly_decompress_d5+0x28>
     +0x1ed: pop    rbx
     +0x1ee: pop    rbp
     +0x1ef: pop    r12
     +0x1f1: ret
 ***)

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [layout_range "mlkem_poly_decompress_d5"];;

(* ------------------------------------------------------------------------- *)
(* The five bytes for eight coefficients, as parts of a 40-bit word.         *)
(* ------------------------------------------------------------------------- *)

let D5_BYTES_STMT =
  `!a n i s j.
        read (memory :> bytes(a,160)) s = n /\ i < 32 /\ j < 5
        ==> read (memory :> bytes8(word_add a (word(5 * i + j)))) s =
            word_subword (word(n DIV 2 EXP (40 * i)):40 word) (8 * j,8)`;;

let D5_BYTES =
  assume_spec D5_BYTES_STMT;;

(* ------------------------------------------------------------------------- *)
(* The computation for each coefficient, with its 5-bit field f in the 40    *)
(* bits, multiplying by 3329 with shifts and additions, and the field as     *)
(* part of the number for the input bytes.                                   *)
(* ------------------------------------------------------------------------- *)

let D5_LANE_STMT =
  `!f:5 word.
     word_subword
      (word_ushr
        (word_add
          (word_shl (word_add (word_shl (word_add (word_shl
             (word_zx f:int32) 1) (word_zx f)) 2) (word_zx f)) 8)
          (word_add (word_zx f) (word 16))) 5) (0,16):int16 =
     word((3329 * val f + 16) DIV 32)`;;

let D5_LANE =
  assume_spec D5_LANE_STMT;;

let D5_FIELD_STMT =
  `!n i k. k < 8
     ==> val(word_subword (word(n DIV 2 EXP (40 * i)):40 word)
                          (5 * k,5):5 word) =
         (n DIV 2 EXP (5 * (8 * i + k))) MOD 32`;;

let D5_FIELD =
  assume_spec D5_FIELD_STMT;;

(*** The stored coefficient k, from its lane of one of the two 64-bit
 *** stores, using the bit-level form of the computation of its 5-bit field
 ***)

let D5_LANE_RULE k th =
  let th1 = CONV_RULE(RAND_CONV(REWRITE_CONV
     [WORD_VAL_MOD_256; WORD_VAL_MOD_65536] THENC SIMD_SIMPLIFY_CONV [])) th in
  let v = rand(concl th1) in
  let f = subst [mk_small_numeral (5 * k),`j:num`]
                `word_subword (w:40 word) (j,5):5 word` in
  let lth = SPEC f D5_LANE in
  let bth = BITBLAST_RULE (mk_eq(v,lhs(concl lth))) in
  CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THENC
                      NUM_REDUCE_CONV))
   (TRANS th1 (TRANS bth lth));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_decompress 5 in                           *)
(* common/fips203/fips203.ml, the result for a 5-bit field y is the integer  *)
(* closest to 3329 * y / 32, rounding up on ties, i.e.                       *)
(* (3329 * y + 16) DIV 32.                                                   *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a n pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        ALL (nonoverlapping (r,512))
            [(word pc,libmlkem_size); (a,160);
             (word_sub stackpointer (word 24),32)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 24),32))
            [(word pc,libmlkem_size); (a,160)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + mlkem_poly_decompress_d5) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,160)) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP (5 * i)) MOD 2 EXP 5 +
                                16) DIV 32))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512);
                         memory :> bytes(word_sub stackpointer
                                                  (word 24),24)])`;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly in the same way.   *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,512))
               [word pc,libmlkem_size; a,160; word_sub stackpointer (word 24),32] /\
           ALL (nonoverlapping (word_sub stackpointer (word 24),32))
               [word pc,libmlkem_size; a,160]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_poly_decompress_d5) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc
                                (word_sub stackpointer (word 24))
                                returnaddress /\
                         memaccess_inbounds e2
                          [a,160; r,512; word (pc + mlkem_poly_decompress_d5_consts),8;
                           word_sub stackpointer (word 24),32]
                          [r,512; word_sub stackpointer (word 24),24]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,512);
                           memory :> bytes(word_sub stackpointer (word 24),
                                           24)])`;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
