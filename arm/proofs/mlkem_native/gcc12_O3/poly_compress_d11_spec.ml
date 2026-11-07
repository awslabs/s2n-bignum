(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of a polynomial to 11 bits per coefficient. This is the code  *)
(* for mlkem_poly_compress_d11 from mlkem-native's portable C implementation *)
(* compiled by gcc 12 with -O3 (see mlkem_native/README.md). It is verified  *)
(* in the whole image (see libmlkem.ml).                                     *)
(*                                                                           *)
(* Unlike at -O2, the code does not go through a temporary array on the     *)
(* stack and has no stack protector, so it uses neither the stack nor the   *)
(* stack guard. The specifications are still those of gcc12_O2, with the    *)
(* 48-byte stack frame and the stack guard, so that the callers can use     *)
(* them in the same way.                                                    *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_compress_d11:
       +0x0: mov     x8, #0x7800
       +0x4: mov     x9, x0
       +0x8: movk    x8, #0x3afb, lsl #16
       +0xc: add     x10, x0, #0x160
      +0x10: movk    x8, #0x1, lsl #32
      +0x14: mov     x7, #0x100000000
      +0x18: nop
      +0x1c: ldrsh   x11, [x1, #2]
      +0x20: add     x9, x9, #0xb
      +0x24: ldrsh   x0, [x1]
      +0x28: add     x1, x1, #0x10
      +0x2c: ldursh  x3, [x1, #-12]
      +0x30: ldursh  x5, [x1, #-10]
      +0x34: madd    x11, x11, x8, x7
      +0x38: ldursh  x4, [x1, #-8]
      +0x3c: madd    x0, x0, x8, x7
      +0x40: ldursh  x2, [x1, #-6]
      +0x44: madd    x3, x3, x8, x7
      +0x48: ldursh  x6, [x1, #-4]
      +0x4c: ubfx    x11, x11, #33, #11
      +0x50: madd    x5, x5, x8, x7
      +0x54: ubfx    x12, x0, #41, #3
      +0x58: ubfx    x0, x0, #33, #11
      +0x5c: orr     w12, w12, w11, lsl #3
      +0x60: fmov    d0, x0
      +0x64: ubfx    x0, x3, #33, #11
      +0x68: fmov    s1, w0
      +0x6c: mov     v0.b[1], w12
      +0x70: ubfx    x5, x5, #33, #11
      +0x74: lsl     w3, w0, #6
      +0x78: ushr    v2.2s, v1.2s, #2
      +0x7c: orr     w11, w3, w11, lsr #5
      +0x80: madd    x4, x4, x8, x7
      +0x84: lsl     w3, w5, #1
      +0x88: madd    x6, x6, x8, x7
      +0x8c: mov     v0.b[2], w11
      +0x90: orr     w3, w3, w0, lsr #10
      +0x94: ubfx    x4, x4, #33, #11
      +0x98: madd    x0, x2, x8, x7
      +0x9c: ldursh  x2, [x1, #-2]
      +0xa0: ubfx    x6, x6, #33, #11
      +0xa4: lsl     w12, w4, #4
      +0xa8: mov     v0.b[3], v2.b[0]
      +0xac: orr     w5, w12, w5, lsr #7
      +0xb0: ubfx    x0, x0, #33, #11
      +0xb4: fmov    s1, w0
      +0xb8: madd    x2, x2, x8, x7
      +0xbc: lsl     w11, w0, #7
      +0xc0: ushr    v1.2s, v1.2s, #1
      +0xc4: mov     v0.b[4], w3
      +0xc8: orr     w4, w11, w4, lsr #4
      +0xcc: ubfx    x2, x2, #33, #11
      +0xd0: lsl     w11, w6, #2
      +0xd4: orr     w0, w11, w0, lsr #9
      +0xd8: sturb   w0, [x9, #-3]
      +0xdc: lsl     w0, w2, #5
      +0xe0: lsr     w2, w2, #3
      +0xe4: mov     v0.b[5], w5
      +0xe8: orr     w6, w0, w6, lsr #6
      +0xec: sturb   w6, [x9, #-2]
      +0xf0: sturb   w2, [x9, #-1]
      +0xf4: mov     v0.b[6], w4
      +0xf8: mov     v0.b[7], v1.b[0]
      +0xfc: stur    d0, [x9, #-11]
     +0x100: cmp     x9, x10
     +0x104: b.ne    <mlkem_poly_compress_d11+0x1c>
     +0x108: ret
 ***)

let MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem_poly_compress_d11"];;

(* ------------------------------------------------------------------------- *)
(* The compression of a coefficient to 11 bits, as computed.                 *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D11_ARITH_STMT =
  `!v. v < 3329
       ==> (4294967296 + v * 5284526080) DIV 8589934592 =
           (4096 * v + 3329) DIV 6658`;;

let COMPRESS_D11_ARITH = assume_spec COMPRESS_D11_ARITH_STMT;;

let WORD_SX_SMALL_64_STMT =
  `!y:int16. val y < 32768 ==> (word_sx y:int64) = word_zx y`;;

let WORD_SX_SMALL_64 = assume_spec WORD_SX_SMALL_64_STMT;;

let COMPRESS_D11_FIELD_STMT =
  `!y:int16.
        val y < 3329
        ==> val(word_subword
                 (word (4294967296 + val (word_sx y:int64) * 5284526080):
                  int64)
                 (33,11):11 word) =
            ((4096 * val y + 3329) DIV 6658) MOD 2048`;;

let COMPRESS_D11_FIELD = assume_spec COMPRESS_D11_FIELD_STMT;;

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

let VAL_JOIN_11X8 = assume_spec VAL_JOIN_11X8_STMT;;

let WORD_SUBWORD_BYTE = prove
 (`!(w:N word) p.
        word_subword w (p,8):byte = word((val w DIV 2 EXP p) MOD 256)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL]);;

(*** The stored bytes as parts of the 88-bit join of the eight fields ***)

let compress_d11_indices = map (fun k ->
  if k = 0 then `8 * i` else
  mk_binop `(+):num->num->num` `8 * i` (mk_small_numeral k)) (0--8);;

let d11_xatoms = map (fun j ->
  vsubst [j,`j:num`]
   `word (4294967296 + val (word_sx ((x:num->int16) j):int64) * 5284526080):
    int64`) (butlast compress_d11_indices);;

let d11_join =
  vsubst (zip d11_xatoms
              (map (fun k -> mk_var("w"^string_of_int k,`:int64`)) (0--7)))
  `word_join (word_subword (w7:int64) (33,11):11 word)
    (word_join (word_subword (w6:int64) (33,11):11 word)
     (word_join (word_subword (w5:int64) (33,11):11 word)
      (word_join (word_subword (w4:int64) (33,11):11 word)
       (word_join (word_subword (w3:int64) (33,11):11 word)
        (word_join (word_subword (w2:int64) (33,11):11 word)
         (word_join (word_subword (w1:int64) (33,11):11 word)
                    (word_subword (w0:int64) (33,11):11 word):22 word):
         33 word):44 word):55 word):66 word):77 word):88 word`;;

let D11_PACK_TAC m =
  let addr =
    if m = 0 then `word_add r (word (11 * i)):int64` else
    mk_comb(mk_comb(`word_add:int64->int64->int64`,`r:int64`),
            mk_comb(`word:num->int64`,
                    mk_binop `(+):num->num->num` `11 * i`
                             (mk_small_numeral m))) in
  let pat = vsubst [addr,`addr:int64`]
              `read (memory :> bytes8 addr) s = x` in
  let rule th =
    let v = rand(concl th) in
    let target = mk_comb(mk_comb(`word_subword:88 word->num#num->byte`,
                                 d11_join),
                         mk_pair(mk_small_numeral(8 * m),`8`)) in
    let gvs = map (fun _ -> genvar `:int64`) d11_xatoms in
    let eq = subst (zip gvs d11_xatoms) (mk_eq(v,target)) in
    TRANS th (INST (zip d11_xatoms gvs) (BITBLAST_RULE eq)) in
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] pat) (concl th)
    then ASSUME_TAC(rule th) else failwith "D11_PACK_TAC");;

(*** The 64-bit store of the first eight bytes, as bytes ***)

let D11_SPLIT_TAC =
  FIRST_X_ASSUM(MP_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
    check (can (term_match []
      `read (memory :> bytes64 (word_add r (word(11 * i)))) s = x`) o
           concl)) THEN
  DISCH_THEN(fun th -> MAP_EVERY (ASSUME_TAC o
     CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD])))
     (CONJUNCTS th));;


(* ------------------------------------------------------------------------- *)
(* The loop body, for eight coefficients, with X1 pointing to them and X9 to *)
(* the eleven bytes for them, both advanced in the body so that some loads   *)
(* and the stores have negative offsets. The first eight bytes are put       *)
(* together in a vector register and stored at once.                         *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D11_BODY_TAC =
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O3_EXEC [k] THEN
    SIMD_SIMPLIFY_TAC[]) (1--57);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_compress 11 in common/fips203.ml, the     *)
(* result for a coefficient x in [0,3329) is the integer closest to          *)
(* 2048 * x / 3329, rounding up on ties, modulo 2048, i.e.                   *)
(* ((4096 * x + 3329) DIV 6658) MOD 2048, and as for mlkem_encode 11 the     *)
(* 11-bit values are put together little-endian. Like the C code, this       *)
(* relies on the coefficients being in [0,3329).                             *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a x guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,352); (a,512); (word_sub stackpointer (word 48),48)] /\
        ALLPAIRS nonoverlapping
         [(r,352); (word_sub stackpointer (word 48),48)]
         [(word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                  read PC s = word (pc + mlkem_poly_compress_d11) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  (!i. i < 256
                       ==> read(memory :> bytes16
                                     (word_add a (word(2 * i)))) s =
                           x i))
             (\s. read PC s = returnaddress /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,352)) s =
                       nsum {i | i < 256}
                            (\i. ((4096 * val(x i) + 3329) DIV 6658) MOD
                                 2048 * 2 EXP (11 * i))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,352);
                         memory :> bytes(word_sub stackpointer
                                                  (word 48),48)])`;;

let MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly as for gcc12_O2,   *)
(* with the regions of the stack frame and the stack guard, which the code   *)
(* does not access.                                                          *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e r a guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [r,352; a,512; word_sub stackpointer (word 48),48] /\
       ALLPAIRS nonoverlapping
        [r,352; word_sub stackpointer (word 48),48]
        [word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O3_mc /\
                 read PC s = word (pc + mlkem_poly_compress_d11) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [r; a] s /\
                 read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                   guard /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events a r guard pc
                           (word_sub stackpointer (word 48)) returnaddress /\
                    memaccess_inbounds e2
                     [a,512; r,352; word_sub stackpointer (word 48),48;
                      word(pc + got_stack_chk_guard),8; guard,8]
                     [r,352; word_sub stackpointer (word 48),48]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(r,352);
                        memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
