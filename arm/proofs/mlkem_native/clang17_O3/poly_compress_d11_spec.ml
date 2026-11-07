(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of a polynomial to 11 bits per coefficient. This is the code  *)
(* for mlkem_poly_compress_d11 from mlkem-native's portable C implementation *)
(* compiled by clang 17 with -O3 (see mlkem_native/README.md). It is         *)
(* verified in the whole image (see libmlkem.ml).                            *)
(*                                                                           *)
(* Unlike at gcc -O2, the code does not go through a temporary array on the  *)
(* stack and has no stack protector, so it uses neither the stack nor the    *)
(* stack guard. The specifications are still those of gcc12_O2, with the     *)
(* 48-byte stack frame and the stack guard, so that the callers can use      *)
(* them in the same way.                                                     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_compress_d11:
       +0x0: mov     x9, #0x7800
       +0x4: mov     x8, xzr
       +0x8: movk    x9, #0x3afb, lsl #16
       +0xc: add     x10, x1, #0xe
      +0x10: movk    x9, #0x1, lsl #32
      +0x14: add     x11, x0, #0x5
      +0x18: mov     x12, #0x100000000
      +0x1c: add     x13, x10, x8
      +0x20: add     x8, x8, #0x10
      +0x24: cmp     x8, #0x200
      +0x28: ldursh  x15, [x13, #-12]
      +0x2c: ldursh  x14, [x13, #-14]
      +0x30: ldursh  x16, [x13, #-10]
      +0x34: madd    x15, x15, x9, x12
      +0x38: ldursh  x0, [x13, #-4]
      +0x3c: madd    x14, x14, x9, x12
      +0x40: ldursh  x17, [x13, #-8]
      +0x44: lsr     x3, x15, #30
      +0x48: madd    x16, x16, x9, x12
      +0x4c: lsr     x2, x14, #33
      +0x50: ubfx    x14, x14, #41, #3
      +0x54: and     w3, w3, #0xf8
      +0x58: ldursh  x18, [x13, #-6]
      +0x5c: orr     w14, w3, w14
      +0x60: lsr     x4, x16, #33
      +0x64: madd    x0, x0, x9, x12
      +0x68: ldursh  x1, [x13, #-2]
      +0x6c: madd    x17, x17, x9, x12
      +0x70: ldrsh   x13, [x13]
      +0x74: madd    x18, x18, x9, x12
      +0x78: lsr     x15, x15, #38
      +0x7c: sturb   w14, [x11, #-4]
      +0x80: lsr     x14, x16, #35
      +0x84: lsr     x3, x0, #33
      +0x88: bfi     w15, w4, #6, #26
      +0x8c: sturb   w2, [x11, #-5]
      +0x90: lsr     x16, x17, #32
      +0x94: lsr     x2, x18, #29
      +0x98: bfxil   w16, w4, #10, #1
      +0x9c: ubfx    x17, x17, #40, #4
      +0xa0: and     w2, w2, #0xf0
      +0xa4: madd    x13, x13, x9, x12
      +0xa8: sturb   w14, [x11, #-2]
      +0xac: lsr     x14, x18, #37
      +0xb0: madd    x1, x1, x9, x12
      +0xb4: sturb   w15, [x11, #-3]
      +0xb8: orr     w15, w2, w17
      +0xbc: bfi     w14, w3, #7, #25
      +0xc0: lsr     x17, x13, #28
      +0xc4: sturb   w16, [x11, #-1]
      +0xc8: lsr     x16, x1, #31
      +0xcc: ubfx    x18, x1, #39, #5
      +0xd0: and     w17, w17, #0xe0
      +0xd4: strb    w15, [x11]
      +0xd8: lsr     x15, x0, #34
      +0xdc: bfxil   w16, w3, #9, #2
      +0xe0: strb    w14, [x11, #1]
      +0xe4: orr     w14, w17, w18
      +0xe8: lsr     x13, x13, #36
      +0xec: strb    w15, [x11, #2]
      +0xf0: strb    w16, [x11, #3]
      +0xf4: strb    w14, [x11, #4]
      +0xf8: strb    w13, [x11, #5]
      +0xfc: add     x11, x11, #0xb
      +0x100: b.ne    <mlkem_poly_compress_d11+0x1c>
      +0x104: ret
 ***)

let MLKEM_NATIVE_POLY_COMPRESS_D11_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
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

let WORD_ADD_2EXP64_STMT =
  `!n. word(n + 18446744073709551616):int64 = word n`;;

let WORD_ADD_2EXP64 = assume_spec WORD_ADD_2EXP64_STMT;;

(*** The loads are at offsets from -14 to 0 from x13 = a + 14 + 16 * i, and
 *** the simulation leaves the sums of the numbers in the address unevaluated,
 *** so the facts about the coefficients are put in that form. ***)

let COMPRESS_D11_ADDR_STMT =
  `!(a:int64) i. word_add a (word(16 * i)) =
         word_add a (word(14 + 16 * i + 18446744073709551602)) /\
         word_add a (word(16 * i + 2)) =
         word_add a (word(14 + 16 * i + 18446744073709551604)) /\
         word_add a (word(16 * i + 4)) =
         word_add a (word(14 + 16 * i + 18446744073709551606)) /\
         word_add a (word(16 * i + 6)) =
         word_add a (word(14 + 16 * i + 18446744073709551608)) /\
         word_add a (word(16 * i + 8)) =
         word_add a (word(14 + 16 * i + 18446744073709551610)) /\
         word_add a (word(16 * i + 10)) =
         word_add a (word(14 + 16 * i + 18446744073709551612)) /\
         word_add a (word(16 * i + 12)) =
         word_add a (word(14 + 16 * i + 18446744073709551614)) /\
         word_add a (word(16 * i + 14)) =
         word_add a (word(14 + 16 * i))`;;

let COMPRESS_D11_ADDR = assume_spec COMPRESS_D11_ADDR_STMT;;

(*** The same for the addresses in the events of the safety proof, which are
 *** put in the form base + offset, for the loads and for the stores. ***)

let COMPRESS_D11_EVENT_ADDR_STMT =
  `(!(a:int64) i. word_add (word_add (word_add a (word 14)) (word(16 * i))) (word 18446744073709551602) =
     word_add a (word(16 * i)) /\
     word_add (word_add (word_add a (word 14)) (word(16 * i))) (word 18446744073709551604) =
     word_add a (word(16 * i + 2)) /\
     word_add (word_add (word_add a (word 14)) (word(16 * i))) (word 18446744073709551606) =
     word_add a (word(16 * i + 4)) /\
     word_add (word_add (word_add a (word 14)) (word(16 * i))) (word 18446744073709551608) =
     word_add a (word(16 * i + 6)) /\
     word_add (word_add (word_add a (word 14)) (word(16 * i))) (word 18446744073709551610) =
     word_add a (word(16 * i + 8)) /\
     word_add (word_add (word_add a (word 14)) (word(16 * i))) (word 18446744073709551612) =
     word_add a (word(16 * i + 10)) /\
     word_add (word_add (word_add a (word 14)) (word(16 * i))) (word 18446744073709551614) =
     word_add a (word(16 * i + 12)) /\
     word_add (word_add a (word 14)) (word(16 * i)) =
     word_add a (word(16 * i + 14))) /\
   (!(r:int64) i. word_add (word_add r (word(11 * i))) (word 1) =
     word_add r (word(11 * i + 1)) /\
     word_add (word_add r (word(11 * i))) (word 2) =
     word_add r (word(11 * i + 2)) /\
     word_add (word_add r (word(11 * i))) (word 3) =
     word_add r (word(11 * i + 3)) /\
     word_add (word_add r (word(11 * i))) (word 4) =
     word_add r (word(11 * i + 4)) /\
     word_add (word_add r (word(11 * i))) (word 5) =
     word_add r (word(11 * i + 5)) /\
     word_add (word_add r (word(11 * i))) (word 6) =
     word_add r (word(11 * i + 6)) /\
     word_add (word_add r (word(11 * i))) (word 7) =
     word_add r (word(11 * i + 7)) /\
     word_add (word_add r (word(11 * i))) (word 8) =
     word_add r (word(11 * i + 8)) /\
     word_add (word_add r (word(11 * i))) (word 9) =
     word_add r (word(11 * i + 9)) /\
     word_add (word_add r (word(11 * i))) (word 10) =
     word_add r (word(11 * i + 10)))`;;

let COMPRESS_D11_EVENT_ADDR = assume_spec COMPRESS_D11_EVENT_ADDR_STMT;;

(* ------------------------------------------------------------------------- *)
(* The loop body, for eight coefficients, with X13 pointing to them (via    *)
(* X10 and X8) and X11 to the eleven bytes for them plus 5, advanced at the  *)
(* end of the body, so that the loads have offsets from -14 to 0 and the     *)
(* stores from -5 to 5.                                                      *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D11_BODY_TAC =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D11_CLANG17_O3_EXEC (1--58);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_compress 11 in common/fips203.ml, the     *)
(* result for a coefficient x in [0,3329) is the integer closest to          *)
(* 2048 * x / 3329, rounding up on ties, modulo 2048, i.e.                   *)
(* ((4096 * x + 3329) DIV 6658) MOD 2048, and as for mlkem_encode 11 the     *)
(* 11-bit values are put together little-endian. Like the C code, this       *)
(* relies on the coefficients being in [0,3329).                             *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_COMPRESS_D11_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
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
                    mlkem_native_libmlkem_clang17_O3_mc /\
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
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE [memory :> bytes(r,352);
                         memory :> bytes(word_sub stackpointer
                                                  (word 48),48)])`;;

let MLKEM_NATIVE_POLY_COMPRESS_D11_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D11_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly as for gcc12_O2,   *)
(* with the regions of the stack frame and the stack guard, which the code   *)
(* does not access.                                                          *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_POLY_COMPRESS_D11_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT =
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
                   mlkem_native_libmlkem_clang17_O3_mc /\
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
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE [memory :> bytes(r,352);
                        memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLKEM_NATIVE_POLY_COMPRESS_D11_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D11_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
