(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of a polynomial to 11 bits per coefficient. This is the code  *)
(* for mlkem_poly_compress_d11 from mlkem-native's portable C implementation *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md). It is verified  *)
(* in the whole image (see libmlkem.ml). The constant vectors that it uses,  *)
(* of 2^32s in 64-bit lanes for the rounding and of masks of 11 bits in      *)
(* 16-bit lanes, are in the image. It saves three registers on the stack, so *)
(* it is verified directly as a subroutine, with that part of the stack.     *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mlkem_native.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_compress_d11:
       +0x0: push   r12
       +0x2: mov    rcx,rdi
       +0x5: pxor   xmm5,xmm5
       +0x9: lea    rdi,[rdi+0x160]
      +0x10: push   rbp
      +0x11: movdqa xmm3,XMMWORD PTR [rip+0x5527]
      +0x19: pxor   xmm4,xmm4
      +0x1d: push   rbx
      +0x1e: movdqa xmm6,XMMWORD PTR [rip+0x552a]
      +0x26: cs     nop WORD PTR [rax+rax*1+0x0]
      +0x30: movdqa xmm2,XMMWORD PTR [rsi]
      +0x34: movdqa xmm0,xmm5
      +0x38: movdqa xmm7,xmm4
      +0x3c: pcmpgtw xmm0,xmm2
      +0x40: movdqa xmm1,xmm2
      +0x44: punpcklwd xmm1,xmm0
      +0x48: punpckhwd xmm2,xmm0
      +0x4c: pcmpgtd xmm7,xmm1
      +0x50: movdqa xmm8,xmm1
      +0x55: punpckldq xmm8,xmm7
      +0x5a: movdqa xmm9,xmm8
      +0x5f: psllq  xmm9,0x2
      +0x65: paddq  xmm9,xmm8
      +0x6a: movdqa xmm0,xmm9
      +0x6f: psllq  xmm0,0x6
      +0x74: psubq  xmm0,xmm9
      +0x79: psllq  xmm0,0x6
      +0x7e: psubq  xmm0,xmm8
      +0x83: psllq  xmm0,0x3
      +0x88: psubq  xmm0,xmm8
      +0x8d: psllq  xmm0,0x4
      +0x92: psubq  xmm0,xmm8
      +0x97: movdqa xmm8,xmm1
      +0x9c: punpckhdq xmm8,xmm7
      +0xa1: psllq  xmm0,0xb
      +0xa6: movdqa xmm7,xmm8
      +0xab: paddq  xmm0,xmm3
      +0xaf: psllq  xmm7,0x2
      +0xb4: psrlq  xmm0,0x21
      +0xb9: paddq  xmm7,xmm8
      +0xbe: movdqa xmm1,xmm7
      +0xc2: psllq  xmm1,0x6
      +0xc7: psubq  xmm1,xmm7
      +0xcb: movdqa xmm7,xmm4
      +0xcf: psllq  xmm1,0x6
      +0xd4: pcmpgtd xmm7,xmm2
      +0xd8: psubq  xmm1,xmm8
      +0xdd: psllq  xmm1,0x3
      +0xe2: psubq  xmm1,xmm8
      +0xe7: psllq  xmm1,0x4
      +0xec: psubq  xmm1,xmm8
      +0xf1: movdqa xmm8,xmm2
      +0xf6: punpckldq xmm8,xmm7
      +0xfb: psllq  xmm1,0xb
     +0x100: movdqa xmm9,xmm8
     +0x105: paddq  xmm1,xmm3
     +0x109: psllq  xmm9,0x2
     +0x10f: psrlq  xmm1,0x21
     +0x114: paddq  xmm9,xmm8
     +0x119: shufps xmm0,xmm1,0x88
     +0x11d: movdqa xmm1,xmm9
     +0x122: psllq  xmm1,0x6
     +0x127: psubq  xmm1,xmm9
     +0x12c: psllq  xmm1,0x6
     +0x131: psubq  xmm1,xmm8
     +0x136: psllq  xmm1,0x3
     +0x13b: psubq  xmm1,xmm8
     +0x140: psllq  xmm1,0x4
     +0x145: psubq  xmm1,xmm8
     +0x14a: movdqa xmm8,xmm2
     +0x14f: punpckhdq xmm8,xmm7
     +0x154: psllq  xmm1,0xb
     +0x159: movdqa xmm7,xmm8
     +0x15e: paddq  xmm1,xmm3
     +0x162: psllq  xmm7,0x2
     +0x167: psrlq  xmm1,0x21
     +0x16c: paddq  xmm7,xmm8
     +0x171: movdqa xmm2,xmm7
     +0x175: psllq  xmm2,0x6
     +0x17a: psubq  xmm2,xmm7
     +0x17e: psllq  xmm2,0x6
     +0x183: psubq  xmm2,xmm8
     +0x188: psllq  xmm2,0x3
     +0x18d: psubq  xmm2,xmm8
     +0x192: psllq  xmm2,0x4
     +0x197: psubq  xmm2,xmm8
     +0x19c: psllq  xmm2,0xb
     +0x1a1: paddq  xmm2,xmm3
     +0x1a5: psrlq  xmm2,0x21
     +0x1aa: shufps xmm1,xmm2,0x88
     +0x1ae: movdqa xmm2,xmm0
     +0x1b2: punpcklwd xmm0,xmm1
     +0x1b6: punpckhwd xmm2,xmm1
     +0x1ba: movdqa xmm1,xmm0
     +0x1be: punpckhwd xmm1,xmm2
     +0x1c2: punpcklwd xmm0,xmm2
     +0x1c6: punpcklwd xmm0,xmm1
     +0x1ca: pand   xmm0,xmm6
     +0x1ce: pextrw r8d,xmm0,0x0
     +0x1d4: pextrw r10d,xmm0,0x1
     +0x1da: pextrw ebx,xmm0,0x2
     +0x1df: mov    r9d,r8d
     +0x1e2: pextrw ebp,xmm0,0x3
     +0x1e7: pextrw eax,xmm0,0x4
     +0x1ec: movzx  r8d,r8b
     +0x1f0: shr    r9w,0x8
     +0x1f5: lea    r12d,[rbp+rbp*1+0x0]
     +0x1fa: pextrw edx,xmm0,0x5
     +0x1ff: shr    bp,0x7
     +0x203: lea    r11d,[r10*8+0x0]
     +0x20b: shr    r10w,0x5
     +0x210: or     r9d,r11d
     +0x213: mov    r11d,ebx
     +0x216: shl    r11d,0x6
     +0x21a: movzx  r9d,r9b
     +0x21e: or     r10d,r11d
     +0x221: mov    r11d,ebx
     +0x224: shr    bx,0xa
     +0x228: or     ebx,r12d
     +0x22b: mov    r12d,eax
     +0x22e: shr    r11w,0x2
     +0x233: movzx  r10d,r10b
     +0x237: shl    r12d,0x4
     +0x23b: movzx  ebx,bl
     +0x23e: movzx  r11d,r11b
     +0x242: or     ebp,r12d
     +0x245: mov    r12d,eax
     +0x248: mov    eax,edx
     +0x24a: shl    eax,0x7
     +0x24d: shr    r12w,0x4
     +0x252: movzx  ebp,bpl
     +0x256: or     r12d,eax
     +0x259: mov    eax,edx
     +0x25b: shr    dx,0x9
     +0x25f: shr    ax,1
     +0x262: movzx  r12d,r12b
     +0x266: movzx  eax,al
     +0x269: shl    rax,0x8
     +0x26d: or     rax,r12
     +0x270: shl    rax,0x8
     +0x274: or     rax,rbp
     +0x277: shl    rax,0x8
     +0x27b: or     rax,rbx
     +0x27e: shl    rax,0x8
     +0x282: or     rax,r11
     +0x285: shl    rax,0x8
     +0x289: or     rax,r10
     +0x28c: shl    rax,0x8
     +0x290: or     rax,r9
     +0x293: shl    rax,0x8
     +0x297: or     rax,r8
     +0x29a: mov    QWORD PTR [rcx],rax
     +0x29d: pextrw eax,xmm0,0x6
     +0x2a2: lea    r8d,[rax*4+0x0]
     +0x2aa: shr    ax,0x6
     +0x2ae: or     edx,r8d
     +0x2b1: mov    BYTE PTR [rcx+0x8],dl
     +0x2b4: pextrw edx,xmm0,0x7
     +0x2b9: mov    r8d,edx
     +0x2bc: shl    r8d,0x5
     +0x2c0: shr    dx,0x3
     +0x2c4: add    rcx,0xb
     +0x2c8: add    rsi,0x10
     +0x2cc: or     eax,r8d
     +0x2cf: mov    BYTE PTR [rcx-0x1],dl
     +0x2d2: mov    BYTE PTR [rcx-0x2],al
     +0x2d5: cmp    rdi,rcx
     +0x2d8: jne    <mlkem_poly_compress_d11+0x30>
     +0x2de: pop    rbx
     +0x2df: pop    rbp
     +0x2e0: pop    r12
     +0x2e2: ret
 ***)

let MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [layout_range "mlkem_poly_compress_d11"];;

(* ------------------------------------------------------------------------- *)
(* The compression of a coefficient to 11 bits, as computed. Each            *)
(* coefficient is sign-extended to 64 bits and multiplied by 5284526080 with *)
(* shifts, additions and subtractions, and the rounding constant 2^32 is     *)
(* added.                                                                    *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D11_ARITH_STMT =
  `!v. v < 3329
       ==> (4294967296 + v * 5284526080) DIV 8589934592 =
           (4096 * v + 3329) DIV 6658`;;

let COMPRESS_D11_ARITH =
  assume_spec COMPRESS_D11_ARITH_STMT;;

let COMPRESS_D11_FIELD_STMT =
  `!y:int16.
        val y < 3329
        ==> let x32:int32 = word_join ((if word_igt (word 0) y
                                        then word 65535 else word 0):int16)
                                      y in
            let x:int64 = word_join ((if word_igt (word 0) x32
                                      then word 4294967295 else word 0):
                                     int32) x32 in
            let t = word_add (word_shl x 2) x in
            val(word_subword
                 (word_add
                   (word_shl
                     (word_sub (word_shl (word_sub (word_shl (word_sub
                       (word_shl (word_sub (word_shl t 6) t) 6) x) 3) x) 4)
                       x) 11)
                   (word 4294967296))
                 (33,11):11 word) =
            ((4096 * val y + 3329) DIV 6658) MOD 2048`;;

let COMPRESS_D11_FIELD =
  assume_spec COMPRESS_D11_FIELD_STMT;;

(* ------------------------------------------------------------------------- *)
(* The packing of eight 11-bit values into eleven bytes.                     *)
(* ------------------------------------------------------------------------- *)

let VAL_JOIN_11X8_STMT =
  `!(u0:11 word) (u1:11 word) (u2:11 word) (u3:11 word)
    (u4:11 word) (u5:11 word) (u6:11 word) (u7:11 word).
     val(word_join u7 (word_join u6 (word_join u5 (word_join u4
          (word_join u3 (word_join u2 (word_join u1 u0:22 word):33 word):
           44 word):55 word):66 word):77 word):88 word) =
     val u0 + 2048 * val u1 + 4194304 * val u2 + 8589934592 * val u3 +
     17592186044416 * val u4 + 36028797018963968 * val u5 +
     73786976294838206464 * val u6 + 151115727451828646838272 * val u7`;;

let VAL_JOIN_11X8 =
  assume_spec VAL_JOIN_11X8_STMT;;

let WORD_SUBWORD_BYTE = prove
 (`!(w:N word) p.
        word_subword w (p,8):byte = word((val w DIV 2 EXP p) MOD 256)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL]);;

(*** The stored bytes as parts of the 88-bit join of the eight fields, with
 *** the computations for the coefficients as atoms for the bit-blasting
 ***)

let compress_d11_indices = map (fun k ->
  if k = 0 then `8 * i` else
  mk_binop `(+):num->num->num` `8 * i` (mk_small_numeral k)) (0--7);;

let d11_xatoms =
  let tm = rand(concl(TOP_DEPTH_CONV let_CONV
   `let x32:int32 = word_join ((if word_igt (word 0) (y:int16)
                                then word 65535 else word 0):int16) y in
    let x:int64 = word_join ((if word_igt (word 0) x32
                              then word 4294967295 else word 0):int32) x32 in
    let t = word_add (word_shl x 2) x in
    word_add
     (word_shl
       (word_sub (word_shl (word_sub (word_shl (word_sub
         (word_shl (word_sub (word_shl t 6) t) 6) x) 3) x) 4) x) 11)
     (word 4294967296)`)) in
  map (fun j -> vsubst [mk_comb(`x:num->int16`,j),`y:int16`] tm)
      compress_d11_indices;;

let d11_join =
  vsubst (zip d11_xatoms (map (fun k -> mk_var("w"^string_of_int k,`:int64`))
                              (0--7)))
  `word_join (word_subword (w7:int64) (33,11):11 word)
    (word_join (word_subword (w6:int64) (33,11):11 word)
     (word_join (word_subword (w5:int64) (33,11):11 word)
      (word_join (word_subword (w4:int64) (33,11):11 word)
       (word_join (word_subword (w3:int64) (33,11):11 word)
        (word_join (word_subword (w2:int64) (33,11):11 word)
         (word_join (word_subword (w1:int64) (33,11):11 word)
                    (word_subword (w0:int64) (33,11):11 word):22 word):
         33 word):44 word):55 word):66 word):77 word):88 word`;;

let D11_PACK_TAC =
  let rule m th =
    let v = rand(concl th) in
    let target = mk_comb(mk_comb(`word_subword:88 word->num#num->byte`,
                                 d11_join),
                         mk_pair(mk_small_numeral(8 * m),`8`)) in
    let gvs = map (fun _ -> genvar `:int64`) d11_xatoms in
    let eq = subst (zip gvs d11_xatoms) (mk_eq(v,target)) in
    let bth = INST (zip d11_xatoms gvs) (BITBLAST_RULE eq) in
    CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THENC
                        NUM_REDUCE_CONV)) (TRANS th bth) in
  fun (asl,w) ->
    let get pat =
      snd(find (fun (_,th) -> can (term_match [] pat) (concl th)) asl) in
    let th8 = get
      `read (memory :> bytes64 (word_add r (word (11 * i)))) s = x`
    and b8 = get
      `read (memory :> bytes8 (word_add r (word (11 * i + 8)))) s = x`
    and b9 = get
      `read (memory :> bytes8 (word_add (word_add r (word (11 * i)))
                                        (word 9))) s = x`
    and b10 = get
      `read (memory :> bytes8 (word_add (word_add r (word (11 * i)))
                                        (word 10))) s = x` in
    let bytes = map (CONV_RULE(RAND_CONV(REWRITE_CONV
                  [WORD_VAL_MOD_256; WORD_VAL_MOD_65536;
                   WORD_VAL_DIV_256_MOD_256] THENC
                  SIMD_SIMPLIFY_CONV [])))
                (CONJUNCTS(CONV_RULE(READ_MEMORY_SPLIT_CONV 3) th8) @
                 [b8; b9; b10]) in
    let olds = map concl [th8; b8; b9; b10] in
    let asl' = filter (fun (_,th) -> not(mem (concl th) olds)) asl in
    MAP_EVERY ASSUME_TAC (map2 rule (0--10) bytes) (asl',w);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_compress 11 in common/fips203/fips203.ml, *)
(* the result for a coefficient x in [0,3329) is the integer closest to      *)
(* 2048 * x / 3329, rounding up on ties, modulo 2048, i.e.                   *)
(* ((4096 * x + 3329) DIV 6658) MOD 2048, and as for mlkem_encode 11 the     *)
(* 11-bit values are put together little-endian. Like the C code, this       *)
(* relies on the coefficients being in [0,3329). The coefficients are read   *)
(* with aligned SSE loads, so the specification requires a to be aligned,    *)
(* as it is in mlkem-native.                                                 *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a x pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\ aligned 16 a /\
        ALL (nonoverlapping (r,352))
            [(word pc,libmlkem_size); (a,512);
             (word_sub stackpointer (word 24),32)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 24),32))
            [(word pc,libmlkem_size); (a,512)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + mlkem_poly_compress_d11) /\
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
                   ==> read(memory :> bytes(r,352)) s =
                       nsum {i | i < 256}
                            (\i. ((4096 * val(x i) + 3329) DIV 6658) MOD
                                 2048 * 2 EXP (11 * i))))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,352);
                         memory :> bytes(word_sub stackpointer
                                                  (word 24),24)])`;;

let MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly in the same way.   *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\ aligned 16 a /\
           ALL (nonoverlapping (r,352))
               [word pc,libmlkem_size; a,512; word_sub stackpointer (word 24),32] /\
           ALL (nonoverlapping (word_sub stackpointer (word 24),32))
               [word pc,libmlkem_size; a,512]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_poly_compress_d11) /\
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
                          [a,512; r,352; word (pc + mlkem_poly_compress_d11_const1),16;
                           word (pc + mlkem_poly_compress_d11_const2),16;
                           word_sub stackpointer (word 24),32]
                          [r,352; word_sub stackpointer (word 24),24]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,352);
                           memory :> bytes(word_sub stackpointer (word 24),
                                           24)])`;;

let MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
