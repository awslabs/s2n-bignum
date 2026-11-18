(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of a polynomial to 11 bits per coefficient. This is the code  *)
(* for mlkem_poly_compress_d11 from mlkem-native's portable C implementation *)
(* compiled by gcc 12 with -Os (see mlkem_native/README.md), with a stack    *)
(* protector. It is verified in the whole image (see                         *)
(* libmlkem.ml), with the address of the stack guard                         *)
(* in the global offset table.                                               *)
(* The code is not vectorized: an outer loop over groups of 8 coefficients   *)
(* computes their 11-bit values by an inner loop into a buffer on the stack  *)
(* and packs them into bytes. The simulation unrolls the inner loop.         *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_compress_d11:
       +0x0: adrp    x2, <page>
       +0x4: ldr     x2, [x2, #4088]  // got_stack_chk_guard
       +0x8: str     x30, [sp, #-48]!
       +0xc: mov     x6, #0x7800
      +0x10: mov     w4, #0x0
      +0x14: movk    x6, #0x3afb, lsl #16
      +0x18: ldr     x3, [x2]
      +0x1c: str     x3, [sp, #40]
      +0x20: mov     x3, #0x0
      +0x24: add     x8, sp, #0x18
      +0x28: movk    x6, #0x1, lsl #32
      +0x2c: mov     x7, #0x100000000
      +0x30: mov     x2, #0x0
      +0x34: add     w3, w4, w2
      +0x38: ldrsh   x3, [x1, x3, lsl #1]
      +0x3c: madd    x3, x3, x6, x7
      +0x40: ubfx    x3, x3, #33, #11
      +0x44: strh    w3, [x8, x2, lsl #1]
      +0x48: add     x2, x2, #0x1
      +0x4c: cmp     x2, #0x8
      +0x50: b.ne    <mlkem_poly_compress_d11+0x34>
      +0x54: ldrh    w3, [sp, #26]
      +0x58: add     w4, w4, #0x8
      +0x5c: ldrh    w2, [sp, #24]
      +0x60: add     x0, x0, #0xb
      +0x64: sturb   w2, [x0, #-11]
      +0x68: lsl     w5, w3, #3
      +0x6c: orr     w2, w5, w2, lsr #8
      +0x70: sturb   w2, [x0, #-10]
      +0x74: ldrh    w2, [sp, #28]
      +0x78: lsl     w5, w2, #6
      +0x7c: orr     w3, w5, w3, lsr #5
      +0x80: ldrh    w5, [sp, #30]
      +0x84: sturb   w3, [x0, #-9]
      +0x88: lsr     w3, w2, #2
      +0x8c: sturb   w3, [x0, #-8]
      +0x90: lsl     w3, w5, #1
      +0x94: orr     w2, w3, w2, lsr #10
      +0x98: ldrh    w3, [sp, #32]
      +0x9c: sturb   w2, [x0, #-7]
      +0xa0: lsl     w2, w3, #4
      +0xa4: orr     w5, w2, w5, lsr #7
      +0xa8: ldrh    w2, [sp, #34]
      +0xac: sturb   w5, [x0, #-6]
      +0xb0: lsl     w5, w2, #7
      +0xb4: orr     w3, w5, w3, lsr #4
      +0xb8: sturb   w3, [x0, #-5]
      +0xbc: lsr     w3, w2, #1
      +0xc0: sturb   w3, [x0, #-4]
      +0xc4: ldrh    w3, [sp, #36]
      +0xc8: lsl     w5, w3, #2
      +0xcc: orr     w2, w5, w2, lsr #9
      +0xd0: sturb   w2, [x0, #-3]
      +0xd4: ldrh    w2, [sp, #38]
      +0xd8: lsl     w5, w2, #5
      +0xdc: lsr     w2, w2, #3
      +0xe0: orr     w3, w5, w3, lsr #6
      +0xe4: sturb   w3, [x0, #-2]
      +0xe8: sturb   w2, [x0, #-1]
      +0xec: cmp     w4, #0x100
      +0xf0: b.ne    <mlkem_poly_compress_d11+0x30>
      +0xf4: adrp    x0, <page>
      +0xf8: ldr     x0, [x0, #4088]  // got_stack_chk_guard
      +0xfc: ldr     x2, [sp, #40]
     +0x100: ldr     x1, [x0]
     +0x104: subs    x2, x2, x1
     +0x108: mov     x1, #0x0
     +0x10c: b.eq    <mlkem_poly_compress_d11+0x114>
     +0x110: bl      <__stack_chk_fail@plt>
     +0x114: ldr     x30, [sp], #48
     +0x118: ret     
 ***)

let MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_Os_mc
   [layout_range "mlkem_poly_compress_d11"];;

(* ------------------------------------------------------------------------- *)
(* The compression of a coefficient to 11 bits, as computed.               *)
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
(* The packing of eight 11-bit values into eleven bytes.                   *)
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

(* * The stored bytes as parts of the 88-bit join of the eight fields **   *)

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

(* ------------------------------------------------------------------------- *)
(* The loops. The inner one, unrolled in the simulation, computes eight    *)
(* 11-bit values into a temporary array on the stack. The index of the     *)
(* coefficient, in X3, is tidied up before it is used as a register offset,  *)
(* as for mlkem_poly_compress_d10.                                         *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D11_INDEX_TAC k =
  let jt = el k compress_d11_indices in
  let wt = mk_comb(`word:num->int64`,jt) in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read X3 s = x`) c then
      MP_TAC th THEN SUBGOAL_THEN (mk_eq(rand c,wt)) SUBST1_TAC THENL
       [WORD_SMALL_TAC; DISCH_TAC] THEN
      SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,wt),jt)) ASSUME_TAC THENL
       [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        UNDISCH_TAC `i < 32` THEN ARITH_TAC;
        ALL_TAC]
    else failwith "COMPRESS_D11_INDEX_TAC");;

(*** The 105 steps of an iteration of the outer loop, up to its test: the
 *** clearing of the index of the inner loop, eight iterations of the inner
 *** loop of 8 instructions each, and the packing of the 8 values ***)

let COMPRESS_D11_BODY_TAC =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_OS_EXEC (1--1) THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_OS_EXEC [2 + 8 * k] THEN
    COMPRESS_D11_INDEX_TAC k THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_OS_EXEC
     ((3 + 8 * k)--(9 + 8 * k))) (0--7) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_OS_EXEC (66--103);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_compress 11 in common/fips203/fips203.ml, *)
(* the result for a coefficient x in [0,3329) is the integer closest to 2048 *)
(* * x / 3329, rounding up on ties, modulo 2048, i.e. ((4096 * x + 3329) DIV *)
(* 6658) MOD 2048, and as for mlkem_encode 11 the 11-bit values are put    *)
(* together little-endian. Like the C code, this relies on the coefficients  *)
(* being in [0,3329). The stack guard is handled as for                    *)
(* mlkem_poly_compress_d4.                                                 *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
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
                    mlkem_native_libmlkem_gcc12_Os_mc /\
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

let MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly as for           *)
(* mlkem_poly_compress_d4.                                                 *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
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
                   mlkem_native_libmlkem_gcc12_Os_mc /\
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

let MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
