(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of a polynomial to 11 bits per coefficient.                   *)
(* This is the code for mlkem_poly_compress_d11 from mlkem-native's portable *)
(* C implementation compiled by gcc 12 with -O2 (see                         *)
(* mlkem_native/README.md). It is verified in the whole image (see           *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x2af0. The    *)
(* constant vectors that it uses, of 2^32s in 64-bit lanes for the rounding  *)
(* and of masks of 11 bits in 16-bit lanes, are at 0x8030 and 0x8040 in the  *)
(* image. It saves three registers on the stack, so it is verified directly  *)
(* as a subroutine, with that part of the stack.                             *)
(* ========================================================================= *)

needs "x86/proofs/utils/mlkem_native.ml";;
needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    2af0: push   r12
    2af2: mov    rcx,rdi
    2af5: pxor   xmm5,xmm5
    2af9: lea    rdi,[rdi+0x160]
    2b00: push   rbp
    2b01: movdqa xmm3,XMMWORD PTR [rip+0x5527]
    2b09: pxor   xmm4,xmm4
    2b0d: push   rbx
    2b0e: movdqa xmm6,XMMWORD PTR [rip+0x552a]
    2b16: cs     nop WORD PTR [rax+rax*1+0x0]
    2b20: movdqa xmm2,XMMWORD PTR [rsi]
    2b24: movdqa xmm0,xmm5
    2b28: movdqa xmm7,xmm4
    2b2c: pcmpgtw xmm0,xmm2
    2b30: movdqa xmm1,xmm2
    2b34: punpcklwd xmm1,xmm0
    2b38: punpckhwd xmm2,xmm0
    2b3c: pcmpgtd xmm7,xmm1
    2b40: movdqa xmm8,xmm1
    2b45: punpckldq xmm8,xmm7
    2b4a: movdqa xmm9,xmm8
    2b4f: psllq  xmm9,0x2
    2b55: paddq  xmm9,xmm8
    2b5a: movdqa xmm0,xmm9
    2b5f: psllq  xmm0,0x6
    2b64: psubq  xmm0,xmm9
    2b69: psllq  xmm0,0x6
    2b6e: psubq  xmm0,xmm8
    2b73: psllq  xmm0,0x3
    2b78: psubq  xmm0,xmm8
    2b7d: psllq  xmm0,0x4
    2b82: psubq  xmm0,xmm8
    2b87: movdqa xmm8,xmm1
    2b8c: punpckhdq xmm8,xmm7
    2b91: psllq  xmm0,0xb
    2b96: movdqa xmm7,xmm8
    2b9b: paddq  xmm0,xmm3
    2b9f: psllq  xmm7,0x2
    2ba4: psrlq  xmm0,0x21
    2ba9: paddq  xmm7,xmm8
    2bae: movdqa xmm1,xmm7
    2bb2: psllq  xmm1,0x6
    2bb7: psubq  xmm1,xmm7
    2bbb: movdqa xmm7,xmm4
    2bbf: psllq  xmm1,0x6
    2bc4: pcmpgtd xmm7,xmm2
    2bc8: psubq  xmm1,xmm8
    2bcd: psllq  xmm1,0x3
    2bd2: psubq  xmm1,xmm8
    2bd7: psllq  xmm1,0x4
    2bdc: psubq  xmm1,xmm8
    2be1: movdqa xmm8,xmm2
    2be6: punpckldq xmm8,xmm7
    2beb: psllq  xmm1,0xb
    2bf0: movdqa xmm9,xmm8
    2bf5: paddq  xmm1,xmm3
    2bf9: psllq  xmm9,0x2
    2bff: psrlq  xmm1,0x21
    2c04: paddq  xmm9,xmm8
    2c09: shufps xmm0,xmm1,0x88
    2c0d: movdqa xmm1,xmm9
    2c12: psllq  xmm1,0x6
    2c17: psubq  xmm1,xmm9
    2c1c: psllq  xmm1,0x6
    2c21: psubq  xmm1,xmm8
    2c26: psllq  xmm1,0x3
    2c2b: psubq  xmm1,xmm8
    2c30: psllq  xmm1,0x4
    2c35: psubq  xmm1,xmm8
    2c3a: movdqa xmm8,xmm2
    2c3f: punpckhdq xmm8,xmm7
    2c44: psllq  xmm1,0xb
    2c49: movdqa xmm7,xmm8
    2c4e: paddq  xmm1,xmm3
    2c52: psllq  xmm7,0x2
    2c57: psrlq  xmm1,0x21
    2c5c: paddq  xmm7,xmm8
    2c61: movdqa xmm2,xmm7
    2c65: psllq  xmm2,0x6
    2c6a: psubq  xmm2,xmm7
    2c6e: psllq  xmm2,0x6
    2c73: psubq  xmm2,xmm8
    2c78: psllq  xmm2,0x3
    2c7d: psubq  xmm2,xmm8
    2c82: psllq  xmm2,0x4
    2c87: psubq  xmm2,xmm8
    2c8c: psllq  xmm2,0xb
    2c91: paddq  xmm2,xmm3
    2c95: psrlq  xmm2,0x21
    2c9a: shufps xmm1,xmm2,0x88
    2c9e: movdqa xmm2,xmm0
    2ca2: punpcklwd xmm0,xmm1
    2ca6: punpckhwd xmm2,xmm1
    2caa: movdqa xmm1,xmm0
    2cae: punpckhwd xmm1,xmm2
    2cb2: punpcklwd xmm0,xmm2
    2cb6: punpcklwd xmm0,xmm1
    2cba: pand   xmm0,xmm6
    2cbe: pextrw r8d,xmm0,0x0
    2cc4: pextrw r10d,xmm0,0x1
    2cca: pextrw ebx,xmm0,0x2
    2ccf: mov    r9d,r8d
    2cd2: pextrw ebp,xmm0,0x3
    2cd7: pextrw eax,xmm0,0x4
    2cdc: movzx  r8d,r8b
    2ce0: shr    r9w,0x8
    2ce5: lea    r12d,[rbp+rbp*1+0x0]
    2cea: pextrw edx,xmm0,0x5
    2cef: shr    bp,0x7
    2cf3: lea    r11d,[r10*8+0x0]
    2cfb: shr    r10w,0x5
    2d00: or     r9d,r11d
    2d03: mov    r11d,ebx
    2d06: shl    r11d,0x6
    2d0a: movzx  r9d,r9b
    2d0e: or     r10d,r11d
    2d11: mov    r11d,ebx
    2d14: shr    bx,0xa
    2d18: or     ebx,r12d
    2d1b: mov    r12d,eax
    2d1e: shr    r11w,0x2
    2d23: movzx  r10d,r10b
    2d27: shl    r12d,0x4
    2d2b: movzx  ebx,bl
    2d2e: movzx  r11d,r11b
    2d32: or     ebp,r12d
    2d35: mov    r12d,eax
    2d38: mov    eax,edx
    2d3a: shl    eax,0x7
    2d3d: shr    r12w,0x4
    2d42: movzx  ebp,bpl
    2d46: or     r12d,eax
    2d49: mov    eax,edx
    2d4b: shr    dx,0x9
    2d4f: shr    ax,1
    2d52: movzx  r12d,r12b
    2d56: movzx  eax,al
    2d59: shl    rax,0x8
    2d5d: or     rax,r12
    2d60: shl    rax,0x8
    2d64: or     rax,rbp
    2d67: shl    rax,0x8
    2d6b: or     rax,rbx
    2d6e: shl    rax,0x8
    2d72: or     rax,r11
    2d75: shl    rax,0x8
    2d79: or     rax,r10
    2d7c: shl    rax,0x8
    2d80: or     rax,r9
    2d83: shl    rax,0x8
    2d87: or     rax,r8
    2d8a: mov    QWORD PTR [rcx],rax
    2d8d: pextrw eax,xmm0,0x6
    2d92: lea    r8d,[rax*4+0x0]
    2d9a: shr    ax,0x6
    2d9e: or     edx,r8d
    2da1: mov    BYTE PTR [rcx+0x8],dl
    2da4: pextrw edx,xmm0,0x7
    2da9: mov    r8d,edx
    2dac: shl    r8d,0x5
    2db0: shr    dx,0x3
    2db4: add    rcx,0xb
    2db8: add    rsi,0x10
    2dbc: or     eax,r8d
    2dbf: mov    BYTE PTR [rcx-0x1],dl
    2dc2: mov    BYTE PTR [rcx-0x2],al
    2dc5: cmp    rdi,rcx
    2dc8: jne    2b20 <mlkem_poly_compress_d11+0x30>
    2dce: pop    rbx
    2dcf: pop    rbp
    2dd0: pop    r12
    2dd2: ret
 ***)

let MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x2af0,0x2dd3];;

(* ------------------------------------------------------------------------- *)
(* The compression of a coefficient to 11 bits, as computed. Each            *)
(* coefficient is sign-extended to 64 bits and multiplied by 5284526080 with *)
(* shifts, additions and subtractions, and the rounding constant 2^32 is     *)
(* added.                                                                    *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D11_ARITH = prove
 (`!v. v < 3329
       ==> (4294967296 + v * 5284526080) DIV 8589934592 =
           (4096 * v + 3329) DIV 6658`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`4096 * v + 3329`; `6658`] DIVISION) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  SPEC_TAC(`(4096 * v + 3329) MOD 6658`,`r:num`) THEN
  SPEC_TAC(`(4096 * v + 3329) DIV 6658`,`q:num`) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN
  EXISTS_TAC `(4294967296 + v * 5284526080) - q * 8589934592` THEN
  ASM_ARITH_TAC);;

let COMPRESS_D11_FIELD = prove
 (`!y:int16.
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
            ((4096 * val y + 3329) DIV 6658) MOD 2048`,
  REPEAT STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_SIMP_TAC[WORD_JOIN_SIGN_SMALL; ARITH_RULE `y < 3329 ==> y < 32768`] THEN
  SUBGOAL_THEN `val(word_zx(y:int16):int32) < 2147483648` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_32] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `y < 3329 ==> y < 4294967296`] THEN
    UNDISCH_TAC `val(y:int16) < 3329` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[WORD_JOIN_SIGN_SMALL_64] THEN
  REWRITE_TAC[WORD_SHL_MUL_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_RULE
   `word_mul (word_sub (word_mul (word_sub (word_mul (word_sub (word_mul
      (word_sub (word_mul (word_add (word_mul x (word 4)) x) (word 64))
      (word_add (word_mul x (word 4)) x)) (word 64)) x) (word 8)) x)
      (word 16)) x) (word 2048):int64 =
    word_mul x (word 5284526080)`] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD_ADD; VAL_WORD_MUL; VAL_WORD_ZX_GEN;
              VAL_WORD; DIMINDEX_64; DIMINDEX_32; DIMINDEX_16] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `y < 3329 ==> y < 4294967296`;
    ARITH_RULE `y < 3329 ==> y < 18446744073709551616`;
    ARITH_RULE `y < 3329 ==> y * 5284526080 < 18446744073709551616`;
    ARITH_RULE `y < 3329
                ==> y * 5284526080 + 4294967296 < 18446744073709551616`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [ADD_SYM] THEN
  ASM_SIMP_TAC[COMPRESS_D11_ARITH]);;

(* ------------------------------------------------------------------------- *)
(* The packing of eight 11-bit values into eleven bytes.                     *)
(* ------------------------------------------------------------------------- *)

let VAL_JOIN_11X8 = prove
 (`!(u0:11 word) (u1:11 word) (u2:11 word) (u3:11 word)
    (u4:11 word) (u5:11 word) (u6:11 word) (u7:11 word).
     val(word_join u7 (word_join u6 (word_join u5 (word_join u4
          (word_join u3 (word_join u2 (word_join u1 u0:22 word):33 word):
           44 word):55 word):66 word):77 word):88 word) =
     val u0 + 2048 * val u1 + 4194304 * val u2 + 8589934592 * val u3 +
     17592186044416 * val u4 + 36028797018963968 * val u5 +
     73786976294838206464 * val u6 + 151115727451828646838272 * val u7`,
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun t -> MP_TAC(ISPEC t VAL_BOUND))
   [`u0:11 word`; `u1:11 word`; `u2:11 word`; `u3:11 word`;
    `u4:11 word`; `u5:11 word`; `u6:11 word`; `u7:11 word`] THEN
  REWRITE_TAC[VAL_WORD_JOIN] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  MAP_EVERY (fun k ->
    SPEC_TAC(mk_comb(`val:11 word->num`,
                     mk_var("u"^string_of_int k,`:11 word`)),
             mk_var("n"^string_of_int k,`:num`))) (0--7) THEN
  REPEAT STRIP_TAC THEN REPEAT MOD_LT_ASM_TAC THEN ARITH_TAC);;

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
(* Correctness proof. As for mlkem_compress 11 in common/fips203.ml, the     *)
(* result for a coefficient x in [0,3329) is the integer closest to          *)
(* 2048 * x / 3329, rounding up on ties, modulo 2048, i.e.                   *)
(* ((4096 * x + 3329) DIV 6658) MOD 2048, and as for mlkem_encode 11 the     *)
(* 11-bit values are put together little-endian. Like the C code, this       *)
(* relies on the coefficients being in [0,3329). The coefficients are read   *)
(* with aligned SSE loads, so the specification requires a to be aligned,    *)
(* as it is in mlkem-native.                                                 *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!r a x pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\ aligned 16 a /\
        ALL (nonoverlapping (r,352))
            [(word pc,0x82a0); (a,512);
             (word_sub stackpointer (word 24),32)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 24),32))
            [(word pc,0x82a0); (a,512)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x2af0) /\
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
                                                  (word 24),24)])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `x:num->int16`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 24 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN

  (*** The loop, over groups of 8 coefficients ***)

  ENSURES_WHILE_UP_TAC `32` `pc + 0x2b20` `pc + 0x2dc5`
   `\i s. read RSI s = word_add a (word(16 * i)) /\
          read RCX s = word_add r (word(11 * i)) /\
          read RDI s = word_add r (word 352) /\
          read XMM3 s = word 0x00000001000000000000000100000000 /\
          read XMM4 s = word 0 /\
          read XMM5 s = word 0 /\
          read XMM6 s = word 0x07ff07ff07ff07ff07ff07ff07ff07ff /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = rbx_init /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s =
          rbp_init /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s =
          r12_init /\
          read (memory :> bytes64 (word_add stackpointer (word 24))) s =
          returnaddress /\
          (!j. j < 256
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   x j) /\
          ((!j. j < 256 ==> val(x j) < 3329)
           ==> read(memory :> bytes(r,11 * i)) s =
               nsum {j | j < 8 * i}
                (\j. ((4096 * val(x j) + 3329) DIV 6658) MOD 2048 *
                     2 EXP (11 * j)))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, saving the registers, with the vectors of       ***)
    (*** constants from the image                                        ***)

    GHOST_INTRO_TAC `ymm3_init:int256` `read YMM3` THEN
    GHOST_INTRO_TAC `ymm4_init:int256` `read YMM4` THEN
    GHOST_INTRO_TAC `ymm5_init:int256` `read YMM5` THEN
    GHOST_INTRO_TAC `ymm6_init:int256` `read YMM6` THEN
    MLKEM_NATIVE_IMAGE_RIPREL_ALIGNED_TAC 0x2b09 0x8030 THEN
    MLKEM_NATIVE_IMAGE_RIPREL_ALIGNED_TAC 0x2b16 0x8040 THEN
    ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP
      (MLKEM_NATIVE_IMAGE_RIPREL_CONST_RULE 0x2b09 0x8030 128)) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP
      (MLKEM_NATIVE_IMAGE_RIPREL_CONST_RULE 0x2b16 0x8040 128)) THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_EXEC (1--10) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[XMM3; XMM4; XMM5; XMM6; READ_ZEROTOP_128] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0;
                NSUM_CLAUSES_NUMSEG_LT; READ_MEMORY_BYTES_TRIVIAL] THEN
    REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST;

    (*** The loop body, for eight coefficients and eleven bytes ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MAP_EVERY (fun n ->
      GHOST_INTRO_TAC (mk_var("ymm"^string_of_int n^"_init",`:int256`))
       (mk_comb(`read:(x86state,int256)component->x86state->int256`,
                mk_const("YMM"^string_of_int n,[])))) [0;1;2;7;8;9] THEN
    ENSURES_INIT_TAC "s0" THEN
    XMM_EXISTSTOP_TAC "top3" `YMM3` THEN
    XMM_EXISTSTOP_TAC "top4" `YMM4` THEN
    XMM_EXISTSTOP_TAC "top5" `YMM5` THEN
    XMM_EXISTSTOP_TAC "top6" `YMM6` THEN
    MP_TAC(SPECL [`a:int64`; `s0:x86state`; `x:num->int16`; `i:num`]
                 READ_MEMORY_BYTES128_JOIN_16) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `aligned 16 (word_add a (word (16 * i)):int64)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC ALIGNED_WORD_ADD THEN
      ASM_REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC NUMBER_RULE;
      ALL_TAC] THEN
    MAP_EVERY (fun k ->
      X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_EXEC [k] THEN
      SIMD_SIMPLIFY_TAC[]) (1--88) THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_EXEC (89--156) THEN

    (*** The new bytes as parts of the join of the 11-bit fields ***)

    D11_PACK_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[XMM3; XMM4; XMM5; XMM6; READ_ZEROTOP_128] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
      CONV_TAC WORD_RULE;
      REWRITE_TAC[ARITH_RULE `11 * (i + 1) = 11 * i + 11`] THEN
      CONV_TAC WORD_RULE;
      CONV_TAC WORD_BLAST;
      CONV_TAC WORD_BLAST;
      CONV_TAC WORD_BLAST;
      CONV_TAC WORD_BLAST;
      ALL_TAC] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[ARITH_RULE `11 * (i + 1) = 11 * i + 11`] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`word_add r (word(11 * i)):int64`; `11`;
                  mk_comb(`val:88 word->num`,d11_join); `s156:x86state`]
                 READ_MEMORY_BYTES_OF_BYTES8) THEN
    ANTS_TAC THENL
     [CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; ADD_CLAUSES;
                  WORD_ADD_0] THEN
      ASM_REWRITE_TAC[WORD_SUBWORD_BYTE] THEN CONV_TAC NUM_REDUCE_CONV;
      DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPEC d11_join VAL_BOUND) THEN
    CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    SIMP_TAC[MOD_LT] THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[VAL_JOIN_11X8] THEN

    (*** The compression of each coefficient ***)

    MAP_EVERY (fun jt ->
      MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)
        (SPEC (mk_comb(`x:num->int16`,jt)) COMPRESS_D11_FIELD)) THEN
      ANTS_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check
         (can (term_match []
                `!j. j < 256 ==> val((x:num->int16) j) < 3329`) o concl)) THEN
        UNDISCH_TAC `i < 32` THEN ARITH_TAC;
        DISCH_THEN SUBST1_TAC]) compress_d11_indices THEN

    (*** The new values in the number for the output ***)

    REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`; NSUM_LT_ADD] THEN
    REWRITE_TAC[NUMSEG_LT; ARITH_EQ] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[ADD_CLAUSES] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC NUM_RING;

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_EXEC (1--2) THEN
    SUBGOAL_THEN
     `~(val(word_sub (word_add r (word 352))
                     (word_add r (word (11 * i))):int64) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[WORD_RULE
       `word_sub (word_add a x) (word_add a y):int64 = word_sub x y`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 32 ==> 11 * i < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `i < 32` THEN ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit, restoring the registers, and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_EXEC (1--2) THEN
    PTR_DECIDE_RIP_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_EXEC (3--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (is_imp o concl))]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly in the same way.   *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\ aligned 16 a /\
           ALL (nonoverlapping (r,352))
               [word pc,0x82a0; a,512; word_sub stackpointer (word 24),32] /\
           ALL (nonoverlapping (word_sub stackpointer (word 24),32))
               [word pc,0x82a0; a,512]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x2af0) /\
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
                          [a,512; r,352; word (pc + 0x8030),16;
                           word (pc + 0x8040),16;
                           word_sub stackpointer (word 24),32]
                          [r,352; word_sub stackpointer (word 24),24]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,352);
                           memory :> bytes(word_sub stackpointer (word 24),
                                           24)])`,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
        (f_ev_epil a r pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 32
            (\i. f_ev_loop a r pc stackpointer returnaddress i))
          (f_ev_prol a r pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `r:int64`; `a:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 24 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + 0x2b20` `pc + 0x2dce`
   `\i s. read RSI s = word_add a (word(16 * i)) /\
          read RCX s = word_add r (word(11 * i)) /\
          read RDI s = word_add r (word 352) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = rbx_init /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s =
          rbp_init /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s =
          r12_init /\
          read (memory :> bytes64 (word_add stackpointer (word 24))) s =
          returnaddress` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    MLKEM_NATIVE_IMAGE_RIPREL_ALIGNED_TAC 0x2b09 0x8030 THEN
    MLKEM_NATIVE_IMAGE_RIPREL_ALIGNED_TAC 0x2b16 0x8040 THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_EXEC (1--10) THEN
    REWRITE_TAC[MULT_0; WORD_ADD_0; WORD_VAL_ADD_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_EXEC (1--4) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `aligned 16 (word_add a (word (16 * i)):int64)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ALIGNED_WORD_ADD THEN
    ASM_REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_EXEC (1--158) THEN
  SUBGOAL_THEN
   `~(val(word_add r (word 352):int64) =
      val(word_add (word_add r (word (11 * i))) (word 11):int64)) <=>
    i + 1 < 32`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_EQ; GSYM WORD_ADD_ASSOC; WORD_ADD_LCANCEL_EQ] THEN
    REWRITE_TAC[GSYM WORD_ADD; WORD_EQ; DIMINDEX_64; CONG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 32 ==> 11 * i + 11 < 18446744073709551616`] THEN
    UNDISCH_TAC `i < 32` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY (fun _ -> CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`;
                ARITH_RULE `11 * (i + 1) = 11 * i + 11`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC]) (1--2) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
