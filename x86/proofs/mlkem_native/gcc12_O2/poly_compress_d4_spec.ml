(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of a polynomial to 4 bits per coefficient. This is the code   *)
(* for mlkem_poly_compress_d4 from mlkem-native's portable C implementation  *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md). It is verified  *)
(* in the whole image (see libmlkem.ml). The constant vectors that it uses,  *)
(* of 2^27s for the rounding and of masks of the low bytes of 16-bit lanes,  *)
(* are in the image.                                                         *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mlkem_native.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_compress_d4:
       +0x0: movq   xmm3,QWORD PTR [rip+0x5b98]
       +0x8: mov    rdx,rsi
       +0xb: mov    rcx,rdi
       +0xe: lea    rsi,[rsi+0x200]
      +0x15: movq   xmm5,QWORD PTR [rip+0x5b8b]
      +0x1d: pxor   xmm4,xmm4
      +0x21: nop    DWORD PTR [rax+0x0]
      +0x28: movq   xmm1,QWORD PTR [rdx]
      +0x2c: movdqa xmm6,xmm4
      +0x30: movq   xmm0,QWORD PTR [rdx+0x8]
      +0x35: movdqa xmm8,xmm4
      +0x3a: add    rdx,0x10
      +0x3e: add    rcx,0x4
      +0x42: pcmpgtw xmm6,xmm1
      +0x46: pcmpgtw xmm8,xmm0
      +0x4b: movdqa xmm7,xmm1
      +0x4f: punpcklwd xmm1,xmm6
      +0x53: punpcklwd xmm7,xmm6
      +0x57: movdqa xmm6,xmm0
      +0x5b: pshufd xmm1,xmm1,0x4e
      +0x60: punpcklwd xmm6,xmm8
      +0x65: movdqa xmm2,xmm1
      +0x69: movdqa xmm1,xmm0
      +0x6d: movdqa xmm0,xmm7
      +0x71: pslld  xmm0,0x6
      +0x76: punpcklwd xmm1,xmm8
      +0x7b: psubd  xmm0,xmm7
      +0x7f: pshufd xmm1,xmm1,0x4e
      +0x84: pslld  xmm0,0x8
      +0x89: psubd  xmm0,xmm7
      +0x8d: movdqa xmm7,xmm2
      +0x91: pslld  xmm7,0x6
      +0x96: psubd  xmm7,xmm2
      +0x9a: pslld  xmm7,0x8
      +0x9f: psubd  xmm7,xmm2
      +0xa3: movdqa xmm2,xmm6
      +0xa7: pslld  xmm2,0x6
      +0xac: psubd  xmm2,xmm6
      +0xb0: pslld  xmm2,0x8
      +0xb5: psubd  xmm2,xmm6
      +0xb9: movdqa xmm6,xmm1
      +0xbd: pslld  xmm6,0x6
      +0xc2: psubd  xmm6,xmm1
      +0xc6: pslld  xmm6,0x8
      +0xcb: psubd  xmm6,xmm1
      +0xcf: movdqa xmm1,xmm0
      +0xd3: pslld  xmm1,0x2
      +0xd8: paddd  xmm1,xmm0
      +0xdc: movdqa xmm0,xmm7
      +0xe0: pslld  xmm0,0x2
      +0xe5: paddd  xmm0,xmm7
      +0xe9: pslld  xmm1,0x4
      +0xee: paddd  xmm1,xmm3
      +0xf2: pslld  xmm0,0x4
      +0xf7: paddd  xmm0,xmm3
      +0xfb: psrld  xmm1,0x1c
     +0x100: movdqa xmm7,xmm1
     +0x104: psrld  xmm0,0x1c
     +0x109: punpcklwd xmm7,xmm0
     +0x10d: punpcklwd xmm1,xmm0
     +0x111: movdqa xmm0,xmm2
     +0x115: pslld  xmm0,0x2
     +0x11a: pshufd xmm7,xmm7,0x4e
     +0x11f: paddd  xmm0,xmm2
     +0x123: movdqa xmm2,xmm6
     +0x127: punpcklwd xmm1,xmm7
     +0x12b: pslld  xmm2,0x2
     +0x130: pand   xmm1,xmm5
     +0x134: paddd  xmm2,xmm6
     +0x138: movdqa xmm7,xmm1
     +0x13c: pslld  xmm0,0x4
     +0x141: paddd  xmm0,xmm3
     +0x145: pslld  xmm2,0x4
     +0x14a: paddd  xmm2,xmm3
     +0x14e: psrld  xmm0,0x1c
     +0x153: movdqa xmm6,xmm0
     +0x157: psrld  xmm2,0x1c
     +0x15c: punpcklwd xmm6,xmm2
     +0x160: punpcklwd xmm0,xmm2
     +0x164: pshufd xmm6,xmm6,0x4e
     +0x169: punpcklwd xmm0,xmm6
     +0x16d: pand   xmm0,xmm5
     +0x171: packuswb xmm7,xmm0
     +0x175: pshufd xmm7,xmm7,0x8
     +0x17a: movq   rax,xmm7
     +0x17f: mov    r8,rax
     +0x182: mov    r9,rax
     +0x185: mov    r10,rax
     +0x188: mov    r11,rax
     +0x18b: shr    r8,0x18
     +0x18f: shr    r9,0x10
     +0x193: movzx  edi,ah
     +0x196: shl    r8d,0x4
     +0x19a: shr    r10,0x20
     +0x19e: shr    r11,0x38
     +0x1a2: or     r8d,r9d
     +0x1a5: mov    r9,rax
     +0x1a8: shl    edi,0x4
     +0x1ab: shr    r9,0x28
     +0x1af: or     edi,eax
     +0x1b1: shr    rax,0x30
     +0x1b5: movzx  r8d,r8b
     +0x1b9: shl    r9d,0x4
     +0x1bd: movzx  edi,dil
     +0x1c1: or     r9d,r10d
     +0x1c4: mov    r10,r11
     +0x1c7: shl    r10d,0x4
     +0x1cb: movzx  r9d,r9b
     +0x1cf: or     eax,r10d
     +0x1d2: movzx  eax,al
     +0x1d5: shl    eax,0x8
     +0x1d8: or     eax,r9d
     +0x1db: shl    eax,0x8
     +0x1de: or     eax,r8d
     +0x1e1: shl    eax,0x8
     +0x1e4: or     eax,edi
     +0x1e6: mov    DWORD PTR [rcx-0x4],eax
     +0x1e9: cmp    rsi,rdx
     +0x1ec: jne    <mlkem_poly_compress_d4+0x28>
     +0x1f2: ret
 ***)

let MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [layout_range "mlkem_poly_compress_d4"];;

(* ------------------------------------------------------------------------- *)
(* The compression of a coefficient to 4 bits, as computed. Each coefficient *)
(* is sign-extended to 32 bits and multiplied by 1290160 with shifts,        *)
(* additions and subtractions, and the rounding constant 2^27 is added.      *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D4_ARITH_STMT =
  `!v. v < 3329
       ==> (134217728 + v * 1290160) DIV 268435456 =
           (32 * v + 3329) DIV 6658`;;

let COMPRESS_D4_ARITH =
  assume_spec COMPRESS_D4_ARITH_STMT;;

let COMPRESS_D4_FIELD_STMT =
  `!y:int16.
        val y < 3329
        ==> let x:int32 = word_join ((if word_igt (word 0) y
                                      then word 65535 else word 0):int16) y in
            let t = word_sub (word_shl (word_sub (word_shl x 6) x) 8) x in
            val(word_subword
                 (word_add (word_shl (word_add (word_shl t 2) t) 4)
                           (word 134217728))
                 (28,4):4 word) =
            ((32 * val y + 3329) DIV 6658) MOD 16`;;

let COMPRESS_D4_FIELD =
  assume_spec COMPRESS_D4_FIELD_STMT;;

(* ------------------------------------------------------------------------- *)
(* The packing of eight 4-bit values into four bytes.                        *)
(* ------------------------------------------------------------------------- *)

let BYTES_OF_NUM_4_STMT =
  `!n. n < 2 EXP 32
       ==> n MOD 256 + 256 * (n DIV 256) MOD 256 +
           65536 * (n DIV 65536) MOD 256 +
           16777216 * (n DIV 16777216) MOD 256 = n`;;

let BYTES_OF_NUM_4 =
  assume_spec BYTES_OF_NUM_4_STMT;;

let VAL_JOIN_4X8_STMT =
  `!(u0:4 word) (u1:4 word) (u2:4 word) (u3:4 word)
    (u4:4 word) (u5:4 word) (u6:4 word) (u7:4 word).
     val(word_join u7 (word_join u6 (word_join u5 (word_join u4
          (word_join u3 (word_join u2 (word_join u1 u0:8 word):12 word):
           16 word):20 word):24 word):28 word):32 word) =
     val u0 + 16 * val u1 + 256 * val u2 + 4096 * val u3 +
     65536 * val u4 + 1048576 * val u5 + 16777216 * val u6 +
     268435456 * val u7`;;

let VAL_JOIN_4X8 =
  assume_spec VAL_JOIN_4X8_STMT;;

(*** The stored bytes as parts of the 32-bit join of the eight fields, with
 *** the computations for the coefficients as atoms for the bit-blasting
 ***)

let compress_d4_indices = map (fun k ->
  if k = 0 then `8 * i` else
  mk_binop `(+):num->num->num` `8 * i` (mk_small_numeral k)) (0--7);;

let d4_xatoms =
  let tm = rand(concl(TOP_DEPTH_CONV let_CONV
   `let x:int32 = word_join ((if word_igt (word 0) (y:int16)
                              then word 65535 else word 0):int16) y in
    let t = word_sub (word_shl (word_sub (word_shl x 6) x) 8) x in
    word_add (word_shl (word_add (word_shl t 2) t) 4) (word 134217728)`)) in
  map (fun j -> vsubst [mk_comb(`x:num->int16`,j),`y:int16`] tm)
      compress_d4_indices;;

let d4_join =
  vsubst (zip d4_xatoms (map (fun k -> mk_var("w"^string_of_int k,`:int32`))
                             (0--7)))
  `word_join (word_subword (w7:int32) (28,4):4 word)
    (word_join (word_subword (w6:int32) (28,4):4 word)
     (word_join (word_subword (w5:int32) (28,4):4 word)
      (word_join (word_subword (w4:int32) (28,4):4 word)
       (word_join (word_subword (w3:int32) (28,4):4 word)
        (word_join (word_subword (w2:int32) (28,4):4 word)
         (word_join (word_subword (w1:int32) (28,4):4 word)
                    (word_subword (w0:int32) (28,4):4 word):8 word):
         12 word):16 word):20 word):24 word):28 word):32 word`;;

let D4_PACK_TAC =
  let rule m th =
    let v = rand(concl th) in
    let target = mk_comb(mk_comb(`word_subword:32 word->num#num->byte`,
                                 d4_join),
                         mk_pair(mk_small_numeral(8 * m),`8`)) in
    let gvs = map (fun _ -> genvar `:int32`) d4_xatoms in
    let eq = subst (zip gvs d4_xatoms) (mk_eq(v,target)) in
    let bth = INST (zip d4_xatoms gvs) (BITBLAST_RULE eq) in
    CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THENC
                        NUM_REDUCE_CONV)) (TRANS th bth) in
  W(fun (asl,w) ->
    let th4 = snd(find (fun (_,th) -> can (term_match []
      `read (memory :> bytes32 (word_add r (word (4 * i)))) s = x`)
      (concl th)) asl) in
    let bytes = map (CONV_RULE(RAND_CONV(REWRITE_CONV
                  [WORD_VAL_MOD_256; WORD_VAL_MOD_65536;
                   WORD_VAL_DIV_256_MOD_256] THENC
                  SIMD_SIMPLIFY_CONV [])))
                (CONJUNCTS(CONV_RULE(READ_MEMORY_SPLIT_CONV 2) th4)) in
    MAP_EVERY ASSUME_TAC (map2 rule (0--3) bytes));;

(* ------------------------------------------------------------------------- *)
(* The two loads of four coefficients, and the bytes of the result of the    *)
(* vector computation, moved to RAX after PACKUSWB.                          *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D4_LOADS_TAC =
  MAP_EVERY (fun k ->
    MP_TAC(SPECL [`a:int64`; `s0:x86state`; `x:num->int16`; k]
                 READ_MEMORY_BYTES64_JOIN_16) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [UNDISCH_TAC `i < 32` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `8 * 2 * i = 16 * i`;
                ARITH_RULE `8 * (2 * i + 1) = 16 * i + 8`;
                ARITH_RULE `4 * 2 * i = 8 * i`;
                ARITH_RULE `4 * (2 * i + 1) = 8 * i + 4`;
                ARITH_RULE `(8 * i + 4) + 1 = 8 * i + 5`;
                ARITH_RULE `(8 * i + 4) + 2 = 8 * i + 6`;
                ARITH_RULE `(8 * i + 4) + 3 = 8 * i + 7`] THEN
    DISCH_TAC) [`2 * i`; `2 * i + 1`];;

let COMPRESS_D4_TIDY_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read RAX s = x`) (concl th) &&
       can (find_term (fun t -> try fst(dest_const(rator t)) = "MIN"
                                with Failure _ -> false)) (concl th)
    then CONV_RULE(RAND_CONV(REWRITE_CONV[PACKUSWB_SAT_255] THENC
                             REWRITE_CONV[PACKUSWB_JOIN] THENC
                             SIMD_SIMPLIFY_CONV [])) th
    else th);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_compress 4 in common/fips203/fips203.ml,  *)
(* the result for a coefficient x in [0,3329) is the integer closest to      *)
(* 16 * x / 3329, rounding up on ties, modulo 16, i.e.                       *)
(* ((32 * x + 3329) DIV 6658) MOD 16, and as for mlkem_encode 4 the 4-bit    *)
(* values are put together little-endian. Like the C code, this relies on    *)
(* the coefficients being in [0,3329).                                       *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_IMAGE_CORRECT_STMT =
  `!r a x pc.
    aligned 16 (word pc:int64) /\
    ALL (nonoverlapping (r,128)) [(word pc,libmlkem_size); (a,512)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
           read RIP s = word (pc + mlkem_poly_compress_d4) /\
           C_ARGUMENTS [r; a] s /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s = x i))
      (\s. read RIP s = word (pc + mlkem_poly_compress_d4_ret) /\
           ((!i. i < 256 ==> val(x i) < 3329)
            ==> read(memory :> bytes(r,128)) s =
                nsum {i | i < 256}
                     (\i. ((32 * val(x i) + 3329) DIV 6658) MOD 16 *
                          2 EXP (4 * i))))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(r,128)])`;;

let MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_IMAGE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_IMAGE_CORRECT_STMT;;

let MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a x pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\
    ALL (nonoverlapping (r,128))
        [(word pc,libmlkem_size); (a,512); (stackpointer,8)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
           read RIP s = word (pc + mlkem_poly_compress_d4) /\
           read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           C_ARGUMENTS [r; a] s /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s = x i))
      (\s. read RIP s = returnaddress /\
           read RSP s = word_add stackpointer (word 8) /\
           ((!i. i < 256 ==> val(x i) < 3329)
            ==> read(memory :> bytes(r,128)) s =
                nsum {i | i < 256}
                     (\i. ((32 * val(x i) + 3329) DIV 6658) MOD 16 *
                          2 EXP (4 * i))))
      (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(r,128)])`;;

let MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_IMAGE_SAFE_STMT =
  `exists f_events.
       forall e r a pc.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,128)) [word pc,libmlkem_size; a,512]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_poly_compress_d4) /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read RIP s = word (pc + mlkem_poly_compress_d4_ret) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc /\
                         memaccess_inbounds e2
                          [a,512; r,128; word (pc + mlkem_poly_compress_d4_const1),8;
                           word (pc + mlkem_poly_compress_d4_const2),8]
                          [r,128]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,128)])`;;

let MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_IMAGE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_IMAGE_SAFE_STMT;;

let MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,128))
               [word pc,libmlkem_size; a,512; stackpointer,8]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_poly_compress_d4) /\
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
                          [a,512; r,128; word (pc + mlkem_poly_compress_d4_const1),8;
                           word (pc + mlkem_poly_compress_d4_const2),8; stackpointer,8]
                          [r,128]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,128)])`;;

let MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
