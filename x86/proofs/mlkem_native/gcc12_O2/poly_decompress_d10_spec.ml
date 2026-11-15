(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of a polynomial from 10 bits per coefficient. This is the   *)
(* code for mlkem_poly_decompress_d10 from mlkem-native's portable C         *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md).  *)
(* It is verified in the whole image (see libmlkem.ml). The constant vector  *)
(* of 512s that it uses for the rounding is in the image.                    *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mlkem_native.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_decompress_d10:
       +0x0: movq   xmm4,QWORD PTR [rip+0x5878]
       +0x8: mov    rdx,rsi
       +0xb: mov    rcx,rdi
       +0xe: pxor   xmm3,xmm3
      +0x12: lea    rsi,[rsi+0x140]
      +0x19: nop    DWORD PTR [rax+0x0]
      +0x20: movzx  r9d,BYTE PTR [rdx+0x1]
      +0x25: movzx  edi,WORD PTR [rdx]
      +0x28: add    rdx,0x5
      +0x2c: add    rcx,0x8
      +0x30: movzx  r10d,BYTE PTR [rdx-0x3]
      +0x35: movzx  eax,BYTE PTR [rdx-0x2]
      +0x39: shr    r9b,0x2
      +0x3d: and    edi,0x3ff
      +0x43: mov    r8d,r10d
      +0x46: movzx  r9d,r9b
      +0x4a: shl    r10d,0x6
      +0x4e: or     r9d,r10d
      +0x51: shr    r8b,0x4
      +0x55: movzx  r10d,al
      +0x59: shl    r10d,0x4
      +0x5d: movzx  r8d,r8b
      +0x61: shr    al,0x6
      +0x64: and    r9d,0x3ff
      +0x6b: or     r8d,r10d
      +0x6e: movzx  r10d,BYTE PTR [rdx-0x1]
      +0x73: movzx  eax,al
      +0x76: and    r8d,0x3ff
      +0x7d: shl    r10d,0x2
      +0x81: or     eax,r10d
      +0x84: movzx  eax,ax
      +0x87: shl    rax,0x10
      +0x8b: or     rax,r8
      +0x8e: shl    rax,0x10
      +0x92: or     rax,r9
      +0x95: shl    rax,0x10
      +0x99: or     rax,rdi
      +0x9c: movq   xmm0,rax
      +0xa1: movdqa xmm2,xmm0
      +0xa5: punpcklwd xmm0,xmm3
      +0xa9: punpcklwd xmm2,xmm3
      +0xad: pshufd xmm0,xmm0,0x4e
      +0xb2: movdqa xmm1,xmm2
      +0xb6: pslld  xmm1,0x1
      +0xbb: paddd  xmm1,xmm2
      +0xbf: pslld  xmm1,0x2
      +0xc4: paddd  xmm1,xmm2
      +0xc8: paddd  xmm2,xmm4
      +0xcc: pslld  xmm1,0x8
      +0xd1: paddd  xmm1,xmm2
      +0xd5: movdqa xmm2,xmm0
      +0xd9: pslld  xmm2,0x1
      +0xde: paddd  xmm2,xmm0
      +0xe2: psrld  xmm1,0xa
      +0xe7: movdqa xmm5,xmm1
      +0xeb: pslld  xmm2,0x2
      +0xf0: paddd  xmm2,xmm0
      +0xf4: paddd  xmm0,xmm4
      +0xf8: pslld  xmm2,0x8
      +0xfd: paddd  xmm2,xmm0
     +0x101: psrld  xmm2,0xa
     +0x106: punpcklwd xmm5,xmm2
     +0x10a: punpcklwd xmm1,xmm2
     +0x10e: pshufd xmm5,xmm5,0x4e
     +0x113: punpcklwd xmm1,xmm5
     +0x117: movq   QWORD PTR [rcx-0x8],xmm1
     +0x11c: cmp    rdx,rsi
     +0x11f: jne    <mlkem_poly_decompress_d10+0x20>
     +0x125: ret
 ***)

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [layout_range "mlkem_poly_decompress_d10"];;

(* ------------------------------------------------------------------------- *)
(* The five bytes for four coefficients, as parts of a 40-bit word. The      *)
(* bytes loaded after the pointer is incremented are at addresses computed   *)
(* from the incremented pointer, so the facts about them are put in that     *)
(* form by D10_ADDR_TAC.                                                     *)
(* ------------------------------------------------------------------------- *)

let D10_BYTES_STMT =
  `!a n i s j.
        read (memory :> bytes(a,320)) s = n /\ i < 64 /\ j < 5
        ==> read (memory :> bytes8(word_add a (word(5 * i + j)))) s =
            word_subword (word(n DIV 2 EXP (40 * i)):40 word) (8 * j,8)`;;

let D10_BYTES =
  assume_spec D10_BYTES_STMT;;

let D10_HALF_STMT =
  `!a n i s.
        read (memory :> bytes(a,320)) s = n /\ i < 64
        ==> read (memory :> bytes16(word_add a (word(5 * i)))) s =
            word_subword (word(n DIV 2 EXP (40 * i)):40 word) (0,16)`;;

let D10_HALF =
  assume_spec D10_HALF_STMT;;

let D10_ADDR_TAC =
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if can (term_match []
         `read (memory :> bytes8 (word_add a (word (5 * i + j)))) s = v`) c &&
       not (can (term_match []
         `read (memory :> bytes8 (word_add a (word (5 * i + 1)))) s = v`) c)
    then CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV
           (REWR_CONV(WORD_RULE `word_add a (word (x + y)):int64 =
                                word_add (word_add a (word x)) (word y)`))))
           th
    else th);;

(* ------------------------------------------------------------------------- *)
(* The computation for each coefficient, with its 10-bit field f in the 40   *)
(* bits, multiplying by 3329 with shifts and additions, and the field as     *)
(* part of the number for the input bytes.                                   *)
(* ------------------------------------------------------------------------- *)

let D10_LANE_STMT =
  `!f:10 word.
     word_subword
      (word_ushr
        (word_add
          (word_shl (word_add (word_shl (word_add (word_shl
             (word_zx f:int32) 1) (word_zx f)) 2) (word_zx f)) 8)
          (word_add (word_zx f) (word 512))) 10) (0,16):int16 =
     word((3329 * val f + 512) DIV 1024)`;;

let D10_LANE =
  assume_spec D10_LANE_STMT;;

let D10_FIELD_STMT =
  `!n i k. k < 4
     ==> val(word_subword (word(n DIV 2 EXP (40 * i)):40 word)
                          (10 * k,10):10 word) =
         (n DIV 2 EXP (10 * (4 * i + k))) MOD 1024`;;

let D10_FIELD =
  assume_spec D10_FIELD_STMT;;

(*** The stored coefficient k, from its lane of the 64-bit store, using the
 *** bit-level form of the computation of its 10-bit field
 ***)

let D10_LANE_RULE k th =
  let th1 = CONV_RULE(RAND_CONV(REWRITE_CONV
     [WORD_VAL_MOD_256; WORD_VAL_MOD_65536] THENC SIMD_SIMPLIFY_CONV [])) th in
  let v = rand(concl th1) in
  let f = subst [mk_small_numeral (10 * k),`j:num`]
                `word_subword (w:40 word) (j,10):10 word` in
  let lth = SPEC f D10_LANE in
  let bth = BITBLAST_RULE (mk_eq(v,lhs(concl lth))) in
  CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THENC
                      NUM_REDUCE_CONV))
   (TRANS th1 (TRANS bth lth));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_decompress 10 in                          *)
(* common/fips203/fips203.ml, the result for a 10-bit field y is the integer *)
(* closest to 3329 * y / 1024, rounding up on ties, i.e.                     *)
(* (3329 * y + 512) DIV 1024.                                                *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_IMAGE_CORRECT_STMT =
  `!r a n pc.
    aligned 16 (word pc:int64) /\
    ALL (nonoverlapping (r,512)) [(word pc,libmlkem_size); (a,320)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
           read RIP s = word (pc + mlkem_poly_decompress_d10) /\
           C_ARGUMENTS [r; a] s /\
           read (memory :> bytes(a,320)) s = n)
      (\s. read RIP s = word (pc + mlkem_poly_decompress_d10_ret) /\
           !i. i < 256
               ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                   word((3329 * (n DIV 2 EXP (10 * i)) MOD 2 EXP 10 + 512)
                        DIV 1024))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_IMAGE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_IMAGE_CORRECT_STMT;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a n pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\
    ALL (nonoverlapping (r,512))
        [(word pc,libmlkem_size); (a,320); (stackpointer,8)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
           read RIP s = word (pc + mlkem_poly_decompress_d10) /\
           read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           C_ARGUMENTS [r; a] s /\
           read (memory :> bytes(a,320)) s = n)
      (\s. read RIP s = returnaddress /\
           read RSP s = word_add stackpointer (word 8) /\
           !i. i < 256
               ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                   word((3329 * (n DIV 2 EXP (10 * i)) MOD 2 EXP 10 + 512)
                        DIV 1024))
      (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_IMAGE_SAFE_STMT =
  `exists f_events.
       forall e r a pc.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; a,320]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_poly_decompress_d10) /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read RIP s = word (pc + mlkem_poly_decompress_d10_ret) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc /\
                         memaccess_inbounds e2
                          [a,320; r,512; word (pc + mlkem_poly_decompress_d10_consts),8] [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_IMAGE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_IMAGE_SAFE_STMT;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,512))
               [word pc,libmlkem_size; a,320; stackpointer,8]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_poly_decompress_d10) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc stackpointer returnaddress /\
                         memaccess_inbounds e2
                          [a,320; r,512; word (pc + mlkem_poly_decompress_d10_consts),8; stackpointer,8]
                          [r,512]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
