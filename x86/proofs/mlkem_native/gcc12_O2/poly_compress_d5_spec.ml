(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of a polynomial to 5 bits per coefficient. This is the code   *)
(* for mlkem_poly_compress_d5 from mlkem-native's portable C implementation  *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md). It is verified  *)
(* in the whole image (see libmlkem.ml). The constant vectors that it uses,  *)
(* of 2^26s for the rounding and of masks of the low bytes of 16-bit lanes,  *)
(* are in the image. It saves two registers on the stack, so it is verified  *)
(* directly as a subroutine, with that part of the stack.                    *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mlkem_native.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_compress_d5:
       +0x0: push   rbp
       +0x1: mov    rcx,rsi
       +0x4: mov    rdx,rdi
       +0x7: lea    rsi,[rdi+0xa0]
       +0xe: movq   xmm2,QWORD PTR [rip+0x5742]
      +0x16: push   rbx
      +0x17: pxor   xmm3,xmm3
      +0x1b: movq   xmm4,QWORD PTR [rip+0x5725]
      +0x23: nop    DWORD PTR [rax+rax*1+0x0]
      +0x28: movq   xmm0,QWORD PTR [rcx]
      +0x2c: movdqa xmm1,xmm3
      +0x30: add    rdx,0x5
      +0x34: add    rcx,0x10
      +0x38: movq   xmm6,QWORD PTR [rcx-0x8]
      +0x3d: pcmpgtw xmm1,xmm0
      +0x41: movdqa xmm9,xmm0
      +0x46: movdqa xmm8,xmm6
      +0x4b: punpcklwd xmm0,xmm1
      +0x4f: punpcklwd xmm9,xmm1
      +0x54: pshufd xmm0,xmm0,0x4e
      +0x59: movdqa xmm10,xmm0
      +0x5e: movdqa xmm0,xmm3
      +0x62: pcmpgtw xmm0,xmm6
      +0x66: movdqa xmm5,xmm10
      +0x6b: pslld  xmm5,0x2
      +0x70: paddd  xmm5,xmm10
      +0x75: punpcklwd xmm8,xmm0
      +0x7a: punpcklwd xmm6,xmm0
      +0x7e: movdqa xmm0,xmm9
      +0x83: pslld  xmm0,0x2
      +0x88: pshufd xmm6,xmm6,0x4e
      +0x8d: movdqa xmm11,xmm8
      +0x92: paddd  xmm0,xmm9
      +0x97: pslld  xmm11,0x2
      +0x9d: movdqa xmm7,xmm6
      +0xa1: paddd  xmm11,xmm8
      +0xa6: pslld  xmm7,0x2
      +0xab: paddd  xmm7,xmm6
      +0xaf: movdqa xmm1,xmm0
      +0xb3: pslld  xmm1,0x6
      +0xb8: psubd  xmm1,xmm0
      +0xbc: movdqa xmm0,xmm5
      +0xc0: pslld  xmm0,0x6
      +0xc5: psubd  xmm0,xmm5
      +0xc9: pslld  xmm1,0x6
      +0xce: psubd  xmm1,xmm9
      +0xd3: pslld  xmm0,0x6
      +0xd8: psubd  xmm0,xmm10
      +0xdd: pslld  xmm1,0x6
      +0xe2: paddd  xmm1,xmm2
      +0xe6: pslld  xmm0,0x6
      +0xeb: paddd  xmm0,xmm2
      +0xef: psrld  xmm1,0x1b
      +0xf4: movdqa xmm5,xmm1
      +0xf8: psrld  xmm0,0x1b
      +0xfd: punpcklwd xmm5,xmm0
     +0x101: punpcklwd xmm1,xmm0
     +0x105: movdqa xmm0,xmm11
     +0x10a: pshufd xmm5,xmm5,0x4e
     +0x10f: pslld  xmm0,0x6
     +0x114: punpcklwd xmm1,xmm5
     +0x118: movdqa xmm5,xmm7
     +0x11c: psubd  xmm0,xmm11
     +0x121: pslld  xmm5,0x6
     +0x126: pand   xmm1,xmm4
     +0x12a: psubd  xmm5,xmm7
     +0x12e: movdqa xmm7,xmm1
     +0x132: pslld  xmm0,0x6
     +0x137: psubd  xmm0,xmm8
     +0x13c: pslld  xmm5,0x6
     +0x141: psubd  xmm5,xmm6
     +0x145: pslld  xmm0,0x6
     +0x14a: paddd  xmm0,xmm2
     +0x14e: pslld  xmm5,0x6
     +0x153: paddd  xmm5,xmm2
     +0x157: psrld  xmm0,0x1b
     +0x15c: movdqa xmm6,xmm0
     +0x160: psrld  xmm5,0x1b
     +0x165: punpcklwd xmm6,xmm5
     +0x169: punpcklwd xmm0,xmm5
     +0x16d: pshufd xmm6,xmm6,0x4e
     +0x172: punpcklwd xmm0,xmm6
     +0x176: pand   xmm0,xmm4
     +0x17a: packuswb xmm7,xmm0
     +0x17e: pshufd xmm7,xmm7,0x8
     +0x183: movq   rax,xmm7
     +0x188: mov    rdi,rax
     +0x18b: mov    rbp,rax
     +0x18e: movzx  ebx,ah
     +0x191: mov    r8,rax
     +0x194: shr    rdi,0x18
     +0x198: shr    rbp,0x10
     +0x19c: mov    r11,rbx
     +0x19f: mov    rbx,rax
     +0x1a2: shl    ebp,0x2
     +0x1a5: mov    r10d,edi
     +0x1a8: shr    rbx,0x20
     +0x1ac: mov    r9,r11
     +0x1af: shl    r10d,0x7
     +0x1b3: shr    r11b,0x3
     +0x1b7: shr    r8,0x30
     +0x1bb: or     r10d,ebp
     +0x1be: shr    dil,1
     +0x1c1: mov    rbp,rax
     +0x1c4: shr    rbp,0x28
     +0x1c8: or     r10d,r11d
     +0x1cb: mov    r11d,ebx
     +0x1ce: shr    bl,0x4
     +0x1d1: shl    r11d,0x4
     +0x1d5: add    ebp,ebp
     +0x1d7: shl    r9d,0x5
     +0x1db: movzx  r10d,r10b
     +0x1df: or     r11d,edi
     +0x1e2: mov    edi,r8d
     +0x1e5: or     r9d,eax
     +0x1e8: shr    rax,0x38
     +0x1ec: shl    edi,0x6
     +0x1ef: movzx  r11d,r11b
     +0x1f3: movzx  r9d,r9b
     +0x1f7: shr    r8b,0x2
     +0x1fb: or     edi,ebp
     +0x1fd: shl    eax,0x3
     +0x200: or     edi,ebx
     +0x202: or     r8d,eax
     +0x205: movzx  edi,dil
     +0x209: mov    BYTE PTR [rdx-0x1],r8b
     +0x20d: shl    edi,0x8
     +0x210: or     edi,r11d
     +0x213: shl    edi,0x8
     +0x216: or     edi,r10d
     +0x219: shl    edi,0x8
     +0x21c: or     edi,r9d
     +0x21f: mov    DWORD PTR [rdx-0x5],edi
     +0x222: cmp    rdx,rsi
     +0x225: jne    <mlkem_poly_compress_d5+0x28>
     +0x22b: pop    rbx
     +0x22c: pop    rbp
     +0x22d: ret
 ***)

let MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [layout_range "mlkem_poly_compress_d5"];;

(* ------------------------------------------------------------------------- *)
(* The compression of a coefficient to 5 bits, as computed. Each coefficient *)
(* is sign-extended to 32 bits and multiplied by 1290176 with shifts,        *)
(* additions and subtractions, and the rounding constant 2^26 is added. As   *)
(* on AArch64, the result of the division is checked for each coefficient.   *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D5_ARITH_STMT =
  `!v. v < 3329
       ==> (67108864 + v * 1290176) DIV 134217728 =
           (64 * v + 3329) DIV 6658`;;

let COMPRESS_D5_ARITH =
  assume_spec COMPRESS_D5_ARITH_STMT;;

let COMPRESS_D5_FIELD_STMT =
  `!y:int16.
        val y < 3329
        ==> let x:int32 = word_join ((if word_igt (word 0) y
                                      then word 65535 else word 0):int16) y in
            val(word_subword
                 (word_add
                   (word_shl
                     (word_sub (word_shl (word_sub (word_shl
                       (word_add (word_shl x 2) x) 6)
                       (word_add (word_shl x 2) x)) 6) x) 6)
                   (word 67108864))
                 (27,5):5 word) =
            ((64 * val y + 3329) DIV 6658) MOD 32`;;

let COMPRESS_D5_FIELD =
  assume_spec COMPRESS_D5_FIELD_STMT;;

(* ------------------------------------------------------------------------- *)
(* The packing of eight 5-bit values into five bytes.                        *)
(* ------------------------------------------------------------------------- *)

let BYTES_OF_NUM_5_STMT =
  `!n. n < 2 EXP 40
       ==> n MOD 256 + 256 * (n DIV 256) MOD 256 +
           65536 * (n DIV 65536) MOD 256 +
           16777216 * (n DIV 16777216) MOD 256 +
           4294967296 * (n DIV 4294967296) MOD 256 = n`;;

let BYTES_OF_NUM_5 =
  assume_spec BYTES_OF_NUM_5_STMT;;

let VAL_JOIN_5X8_STMT =
  `!(u0:5 word) (u1:5 word) (u2:5 word) (u3:5 word)
    (u4:5 word) (u5:5 word) (u6:5 word) (u7:5 word).
     val(word_join u7 (word_join u6 (word_join u5 (word_join u4
          (word_join u3 (word_join u2 (word_join u1 u0:10 word):15 word):
           20 word):25 word):30 word):35 word):40 word) =
     val u0 + 32 * val u1 + 1024 * val u2 + 32768 * val u3 +
     1048576 * val u4 + 33554432 * val u5 + 1073741824 * val u6 +
     34359738368 * val u7`;;

let VAL_JOIN_5X8 =
  assume_spec VAL_JOIN_5X8_STMT;;

(*** The stored bytes as parts of the 40-bit join of the eight fields, with
 *** the computations for the coefficients as atoms for the bit-blasting
 ***)

let compress_d5_indices = map (fun k ->
  if k = 0 then `8 * i` else
  mk_binop `(+):num->num->num` `8 * i` (mk_small_numeral k)) (0--7);;

let d5_xatoms =
  let tm = rand(concl(TOP_DEPTH_CONV let_CONV
   `let x:int32 = word_join ((if word_igt (word 0) (y:int16)
                              then word 65535 else word 0):int16) y in
    word_add
     (word_shl
       (word_sub (word_shl (word_sub (word_shl
         (word_add (word_shl x 2) x) 6)
         (word_add (word_shl x 2) x)) 6) x) 6)
     (word 67108864)`)) in
  map (fun j -> vsubst [mk_comb(`x:num->int16`,j),`y:int16`] tm)
      compress_d5_indices;;

let d5_join =
  vsubst (zip d5_xatoms (map (fun k -> mk_var("w"^string_of_int k,`:int32`))
                             (0--7)))
  `word_join (word_subword (w7:int32) (27,5):5 word)
    (word_join (word_subword (w6:int32) (27,5):5 word)
     (word_join (word_subword (w5:int32) (27,5):5 word)
      (word_join (word_subword (w4:int32) (27,5):5 word)
       (word_join (word_subword (w3:int32) (27,5):5 word)
        (word_join (word_subword (w2:int32) (27,5):5 word)
         (word_join (word_subword (w1:int32) (27,5):5 word)
                    (word_subword (w0:int32) (27,5):5 word):10 word):
         15 word):20 word):25 word):30 word):35 word):40 word`;;

let D5_PACK_TAC =
  let rule m th =
    let v = rand(concl th) in
    let target = mk_comb(mk_comb(`word_subword:40 word->num#num->byte`,
                                 d5_join),
                         mk_pair(mk_small_numeral(8 * m),`8`)) in
    let gvs = map (fun _ -> genvar `:int32`) d5_xatoms in
    let eq = subst (zip gvs d5_xatoms) (mk_eq(v,target)) in
    let bth = INST (zip d5_xatoms gvs) (BITBLAST_RULE eq) in
    CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THENC
                        NUM_REDUCE_CONV)) (TRANS th bth) in
  W(fun (asl,w) ->
    let get pat =
      snd(find (fun (_,th) -> can (term_match [] pat) (concl th)) asl) in
    let th4 = get
      `read (memory :> bytes32 (word_add r (word (5 * i)))) s = x`
    and th1 = get
      `read (memory :> bytes8 (word_add (word_add r (word (5 * i)))
                                        (word 4))) s = x` in
    let bytes = map (CONV_RULE(RAND_CONV(REWRITE_CONV
                  [WORD_VAL_MOD_256; WORD_VAL_MOD_65536;
                   WORD_VAL_DIV_256_MOD_256] THENC
                  SIMD_SIMPLIFY_CONV [])))
                (CONJUNCTS(CONV_RULE(READ_MEMORY_SPLIT_CONV 2) th4) @ [th1]) in
    MAP_EVERY ASSUME_TAC (map2 rule (0--4) bytes));;

(* ------------------------------------------------------------------------- *)
(* The two loads of four coefficients, and the bytes of the result of the    *)
(* vector computation, moved to RAX after PACKUSWB.                          *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D5_LOADS_TAC =
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
    REWRITE_TAC[WORD_RULE
     `word_add a (word (16 * i + 8)):int64 =
      word_add (word_add a (word (16 * i))) (word 8)`] THEN
    DISCH_TAC) [`2 * i`; `2 * i + 1`];;

let COMPRESS_D5_TIDY_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read RAX s = x`) (concl th) &&
       can (find_term (fun t -> try fst(dest_const(rator t)) = "MIN"
                                with Failure _ -> false)) (concl th)
    then CONV_RULE(RAND_CONV(REWRITE_CONV[PACKUSWB_SAT_255] THENC
                             REWRITE_CONV[PACKUSWB_JOIN] THENC
                             SIMD_SIMPLIFY_CONV [])) th
    else th);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_compress 5 in common/fips203/fips203.ml,  *)
(* the result for a coefficient x in [0,3329) is the integer closest to      *)
(* 32 * x / 3329, rounding up on ties, modulo 32, i.e.                       *)
(* ((64 * x + 3329) DIV 6658) MOD 32, and as for mlkem_encode 5 the 5-bit    *)
(* values are put together little-endian. Like the C code, this relies on    *)
(* the coefficients being in [0,3329).                                       *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a x pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        ALL (nonoverlapping (r,160))
            [(word pc,libmlkem_size); (a,512);
             (word_sub stackpointer (word 16),24)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 16),24))
            [(word pc,libmlkem_size); (a,512)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + mlkem_poly_compress_d5) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes16
                                     (word_add a (word(2 * i)))) s =
                           x i))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,160)) s =
                       nsum {i | i < 256}
                            (\i. ((64 * val(x i) + 3329) DIV 6658) MOD 32 *
                                 2 EXP (5 * i))))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,160);
                         memory :> bytes(word_sub stackpointer
                                                  (word 16),16)])`;;

let MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly in the same way.   *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,160))
               [word pc,libmlkem_size; a,512; word_sub stackpointer (word 16),24] /\
           ALL (nonoverlapping (word_sub stackpointer (word 16),24))
               [word pc,libmlkem_size; a,512]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_poly_compress_d5) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc
                                (word_sub stackpointer (word 16))
                                returnaddress /\
                         memaccess_inbounds e2
                          [a,512; r,160; word (pc + mlkem_poly_compress_d5_const2),8;
                           word (pc + mlkem_poly_compress_d5_const1),8;
                           word_sub stackpointer (word 16),24]
                          [r,160; word_sub stackpointer (word 16),16]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,160);
                           memory :> bytes(word_sub stackpointer (word 16),
                                           16)])`;;

let MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
