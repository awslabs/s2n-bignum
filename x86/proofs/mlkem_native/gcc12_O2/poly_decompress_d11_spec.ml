(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of a polynomial from 11 bits per coefficient. This is the   *)
(* code for mlkem_poly_decompress_d11 from mlkem-native's portable C         *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md).  *)
(* It is verified in the whole image (see libmlkem.ml). The constant vectors *)
(* of 3329s and 1024s that it uses are in the image. It saves four registers *)
(* on the stack, so it is verified directly as a subroutine, with that part  *)
(* of the stack.                                                             *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mlkem_native.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_decompress_d11:
       +0x0: movdqa xmm4,XMMWORD PTR [rip+0x5068]
       +0x8: movdqa xmm3,XMMWORD PTR [rip+0x5070]
      +0x10: push   r13
      +0x12: push   r12
      +0x14: push   rbp
      +0x15: lea    rbp,[rsi+0x160]
      +0x1c: push   rbx
      +0x1d: mov    rbx,rdi
      +0x20: mov    rdi,rsi
      +0x23: nop    DWORD PTR [rax+rax*1+0x0]
      +0x28: movzx  r10d,BYTE PTR [rdi+0x1]
      +0x2d: movzx  r8d,BYTE PTR [rdi+0x2]
      +0x32: movzx  r9d,BYTE PTR [rdi+0x4]
      +0x37: movzx  r13d,BYTE PTR [rdi+0x3]
      +0x3c: shr    r10b,0x3
      +0x40: mov    r11d,r8d
      +0x43: shl    r8d,0x5
      +0x47: movzx  eax,BYTE PTR [rdi+0x5]
      +0x4b: movzx  r10d,r10b
      +0x4f: shl    r13d,0x2
      +0x53: movzx  r12d,BYTE PTR [rdi+0x6]
      +0x58: movzx  ecx,WORD PTR [rdi]
      +0x5b: or     r10d,r8d
      +0x5e: mov    r8d,r9d
      +0x61: shr    r11b,0x6
      +0x65: movzx  edx,BYTE PTR [rdi+0x8]
      +0x69: shl    r8d,0xa
      +0x6d: movzx  r11d,r11b
      +0x71: shr    r9b,1
      +0x74: movzx  esi,BYTE PTR [rdi+0x9]
      +0x78: or     r8d,r13d
      +0x7b: movzx  r9d,r9b
      +0x7f: movzx  r13d,BYTE PTR [rdi+0x7]
      +0x84: and    cx,0x7ff
      +0x89: or     r8d,r11d
      +0x8c: movzx  r11d,al
      +0x90: shr    al,0x4
      +0x93: and    r10w,0x7ff
      +0x99: shl    r11d,0x7
      +0x9d: movzx  eax,al
      +0xa0: add    r13d,r13d
      +0xa3: and    r8w,0x7ff
      +0xa9: or     r9d,r11d
      +0xac: movd   xmm1,ecx
      +0xb0: movd   xmm5,r8d
      +0xb5: movzx  r11d,r12b
      +0xb9: shl    r11d,0x4
      +0xbd: shr    r12b,0x7
      +0xc1: and    r9w,0x7ff
      +0xc7: pinsrw xmm1,r10d,0x1
      +0xcd: or     eax,r11d
      +0xd0: mov    r11d,edx
      +0xd3: movzx  r12d,r12b
      +0xd7: shr    dl,0x2
      +0xda: shl    r11d,0x9
      +0xde: movzx  edx,dl
      +0xe1: and    ax,0x7ff
      +0xe5: or     r11d,r13d
      +0xe8: movd   xmm0,eax
      +0xec: pinsrw xmm5,r9d,0x1
      +0xf2: or     r11d,r12d
      +0xf5: movzx  r12d,sil
      +0xf9: shr    sil,0x5
      +0xfd: punpckldq xmm1,xmm5
     +0x101: shl    r12d,0x6
     +0x105: movzx  esi,sil
     +0x109: and    r11w,0x7ff
     +0x10f: or     edx,r12d
     +0x112: movzx  r12d,BYTE PTR [rdi+0xa]
     +0x117: pinsrw xmm0,r11d,0x1
     +0x11d: and    dx,0x7ff
     +0x122: shl    r12d,0x3
     +0x126: movd   xmm2,edx
     +0x12a: or     esi,r12d
     +0x12d: add    rdi,0xb
     +0x131: add    rbx,0x10
     +0x135: pinsrw xmm2,esi,0x1
     +0x13a: punpckldq xmm0,xmm2
     +0x13e: movdqa xmm2,xmm4
     +0x142: punpcklqdq xmm1,xmm0
     +0x146: pmullw xmm2,xmm1
     +0x14a: pmulhuw xmm1,xmm4
     +0x14e: movdqa xmm0,xmm2
     +0x152: punpckhwd xmm2,xmm1
     +0x156: punpcklwd xmm0,xmm1
     +0x15a: movdqa xmm1,xmm2
     +0x15e: paddd  xmm0,xmm3
     +0x162: paddd  xmm1,xmm3
     +0x166: psrld  xmm1,0xb
     +0x16b: psrld  xmm0,0xb
     +0x170: movdqa xmm2,xmm0
     +0x174: punpcklwd xmm0,xmm1
     +0x178: punpckhwd xmm2,xmm1
     +0x17c: movdqa xmm1,xmm0
     +0x180: punpckhwd xmm1,xmm2
     +0x184: punpcklwd xmm0,xmm2
     +0x188: punpcklwd xmm0,xmm1
     +0x18c: movaps XMMWORD PTR [rbx-0x10],xmm0
     +0x190: cmp    rbp,rdi
     +0x193: jne    <mlkem_poly_decompress_d11+0x28>
     +0x199: pop    rbx
     +0x19a: pop    rbp
     +0x19b: pop    r12
     +0x19d: pop    r13
     +0x19f: ret
 ***)

let MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [layout_range "mlkem_poly_decompress_d11"];;

(* ------------------------------------------------------------------------- *)
(* The eleven bytes for eight coefficients, as parts of an 88-bit word.      *)
(* ------------------------------------------------------------------------- *)

let D11_BYTES_STMT =
  `!a n i s j.
        read (memory :> bytes(a,352)) s = n /\ i < 32 /\ j < 11
        ==> read (memory :> bytes8(word_add a (word(11 * i + j)))) s =
            word_subword (word(n DIV 2 EXP (88 * i)):88 word) (8 * j,8)`;;

let D11_BYTES =
  assume_spec D11_BYTES_STMT;;

let D11_HALF_STMT =
  `!a n i s.
        read (memory :> bytes(a,352)) s = n /\ i < 32
        ==> read (memory :> bytes16(word_add a (word(11 * i)))) s =
            word_subword (word(n DIV 2 EXP (88 * i)):88 word) (0,16)`;;

let D11_HALF =
  assume_spec D11_HALF_STMT;;

(* ------------------------------------------------------------------------- *)
(* The computation for each coefficient, with its 11-bit field f in the 88   *)
(* bits, and the field as part of the number for the input bytes. The        *)
(* products by 3329 are computed with PMULLW and PMULHUW, giving their low   *)
(* and high halves, which are put together as 32-bit products.               *)
(* ------------------------------------------------------------------------- *)

let D11D_LANE_STMT =
  `!f:11 word.
     word_subword
      (word_ushr
        (word_add
          (word_mul (word_zx (word_zx f:int16):int32) (word 3329))
          (word 1024)) 11) (0,16):int16 =
     word((3329 * val f + 1024) DIV 2048)`;;

let D11D_LANE =
  assume_spec D11D_LANE_STMT;;

let D11D_FIELD_STMT =
  `!n i k. k < 8
     ==> val(word_subword (word(n DIV 2 EXP (88 * i)):88 word)
                          (11 * k,11):11 word) =
         (n DIV 2 EXP (11 * (8 * i + k))) MOD 2048`;;

let D11D_FIELD =
  assume_spec D11D_FIELD_STMT;;

let WORD_JOIN_MULHU_MULLO_STMT =
  `!x y:int16.
        word_join (word_subword (word_mul (word_zx x:int32) (word_zx y:int32))
                                (16,16):int16)
                  (word_mul x y:int16):int32 =
        word_mul (word_zx x) (word_zx y)`;;

let WORD_JOIN_MULHU_MULLO =
  assume_spec WORD_JOIN_MULHU_MULLO_STMT;;

let WORD_JOIN_MULHU_MULLO_3329_STMT =
  `!x:int16.
        word_join (word_subword (word_mul (word_zx x:int32) (word 3329))
                                (16,16):int16)
                  (word_mul (word 3329) x:int16):int32 =
        word_mul (word_zx x) (word 3329)`;;

let WORD_JOIN_MULHU_MULLO_3329 =
  assume_spec WORD_JOIN_MULHU_MULLO_3329_STMT;;

(*** The stored coefficient k, from its lane of the 128-bit store, with the
 *** extraction of its 11-bit field checked by bit-blasting
 ***)

let D11_LANE_RULE k th =
  let th1 = CONV_RULE(RAND_CONV(REWRITE_CONV[WORD_VAL_MOD_256;
                                             WORD_VAL_MOD_65536] THENC
                                SIMD_SIMPLIFY_CONV [] THENC
                                REWRITE_CONV[WORD_JOIN_MULHU_MULLO_3329]))
              th in
  let v = rand(concl th1) in
  let m = find_term (can (term_match []
            `word_mul (word_zx (t:int16):int32) (word 3329)`)) v in
  let t = rand(lhand m) in
  let f = subst [mk_small_numeral (11 * k),`j:num`]
                `word_subword (w:88 word) (j,11):11 word` in
  let tth = BITBLAST_RULE (mk_eq(t,mk_comb(`word_zx:11 word->int16`,f))) in
  let th2 = CONV_RULE(RAND_CONV(REWRITE_CONV[tth; D11D_LANE])) th1 in
  CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THENC
                      NUM_REDUCE_CONV)) th2;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_decompress 11 in                          *)
(* common/fips203/fips203.ml, the result for an 11-bit field y is the        *)
(* integer closest to 3329 * y / 2048, rounding up on ties, i.e.             *)
(* (3329 * y + 1024) DIV 2048. The result is written with aligned SSE        *)
(* stores, so the specification requires r to be aligned, as it is in        *)
(* mlkem-native.                                                             *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a n pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\ aligned 16 r /\
        ALL (nonoverlapping (r,512))
            [(word pc,libmlkem_size); (a,352);
             (word_sub stackpointer (word 32),40)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),40))
            [(word pc,libmlkem_size); (a,352)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + mlkem_poly_decompress_d11) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,352)) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP (11 * i)) MOD 2 EXP 11 +
                                1024) DIV 2048))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512);
                         memory :> bytes(word_sub stackpointer
                                                  (word 32),32)])`;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly in the same way.   *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\ aligned 16 r /\
           ALL (nonoverlapping (r,512))
               [word pc,libmlkem_size; a,352; word_sub stackpointer (word 32),40] /\
           ALL (nonoverlapping (word_sub stackpointer (word 32),40))
               [word pc,libmlkem_size; a,352]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_poly_decompress_d11) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc
                                (word_sub stackpointer (word 32))
                                returnaddress /\
                         memaccess_inbounds e2
                          [a,352; r,512; word (pc + mlkem_poly_decompress_d11_const1),16;
                           word (pc + mlkem_poly_decompress_d11_const2),16;
                           word_sub stackpointer (word 32),40]
                          [r,512; word_sub stackpointer (word 32),32]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,512);
                           memory :> bytes(word_sub stackpointer (word 32),
                                           32)])`;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
