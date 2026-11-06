(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Centered binomial distribution with eta = 3. This is the code for         *)
(* mlkem_poly_cbd3 from mlkem-native's portable C implementation compiled by *)
(* gcc 12 with -O2 (see mlkem_native/README.md). It is verified in the whole *)
(* image (see libmlkem.ml), with vectors of shifts.                          *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_cbd3:
       +0x0: mov     x2, x1
       +0x4: mov     x4, x0
       +0x8: adrp    x1, <page>
       +0xc: adrp    x0, <page>
      +0x10: movi    v2.4h, #0x7
      +0x14: mov     w3, #0x9249
      +0x18: ldr     q4, [x1, #656]
      +0x1c: add     x6, x2, #0xc0
      +0x20: ldr     q3, [x0, #672]
      +0x24: movk    w3, #0x24, lsl #16
      +0x28: nop
      +0x2c: ldrb    w0, [x2, #2]
      +0x30: add     x2, x2, #0x3
      +0x34: ldurb   w1, [x2, #-2]
      +0x38: ldurb   w5, [x2, #-3]
      +0x3c: lsl     w0, w0, #16
      +0x40: orr     w1, w0, w1, lsl #8
      +0x44: orr     w1, w1, w5
      +0x48: and     w5, w1, w3
      +0x4c: and     w0, w3, w1, lsr #1
      +0x50: and     w1, w3, w1, lsr #2
      +0x54: add     w0, w0, w1
      +0x58: add     w0, w0, w5
      +0x5c: dup     v0.4s, w0
      +0x60: ushl    v1.4s, v0.4s, v4.4s
      +0x64: ushl    v0.4s, v0.4s, v3.4s
      +0x68: xtn     v1.4h, v1.4s
      +0x6c: xtn     v0.4h, v0.4s
      +0x70: and     v1.8b, v1.8b, v2.8b
      +0x74: and     v0.8b, v0.8b, v2.8b
      +0x78: sub     v0.4h, v1.4h, v0.4h
      +0x7c: str     d0, [x4], #8
      +0x80: cmp     x6, x2
      +0x84: b.ne    <mlkem_poly_cbd3+0x2c>
      +0x88: ret
 ***)

let MLKEM_NATIVE_POLY_CBD3_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [layout_range "mlkem_poly_cbd3"];;

(*** The vectors of 32-bit shifts, negative for right shifts ***)

let MLKEM_NATIVE_POLY_CBD3_GCC12_O2_CONSTANTS =
  map (fun d -> MLKEM_NATIVE_IMAGE_CONST_RULE d 128)
   [layout "mlkem_poly_cbd3_const1"; layout "mlkem_poly_cbd3_const2"];;

(*** The three bytes for four coefficients, as parts of a 24-bit word ***)

let CBD3_BYTES_STMT =
  `!a n i s j.
        read (memory :> bytes(a,192)) s = n /\ i < 64 /\ j < 3
        ==> read (memory :> bytes8(word_add a (word(3 * i + j)))) s =
            word_subword (word(n DIV 2 EXP (24 * i)):24 word) (8 * j,8)`;;

let CBD3_BYTES = assume_spec CBD3_BYTES_STMT;;

(* ------------------------------------------------------------------------- *)
(* Each iteration takes three bytes as a 24-bit word t and adds its groups   *)
(* of three bits. Coefficient j of 4 is computed from the sum shifted right  *)
(* by 6 * j and 6 * j + 3, which depends only on the 6-bit field j of t.     *)
(* Below, the computation on a 6-bit field is checked for all its values and *)
(* related to the bits of the number for the input bytes, as for             *)
(* mlkem_poly_cbd2.                                                          *)
(* ------------------------------------------------------------------------- *)

let SIXBIT_BIT_STMT =
  `!n m k. k < 6
           ==> (n DIV 2 EXP (m + k)) MOD 2 =
               (((n DIV 2 EXP m) MOD 64) DIV 2 EXP k) MOD 2`;;

let SIXBIT_BIT = assume_spec SIXBIT_BIT_STMT;;

let CBD3_FIELD_STMT =
  `!m. m < 64
       ==> word_sub
            (word_zx (word_add (word_add (word_and (word m:6 word) (word 1))
                                         (word_and (word_ushr (word m) 1)
                                                   (word 1)))
                               (word_and (word_ushr (word m) 2) (word 1))))
            (word_zx (word_add (word_add (word_and (word_ushr (word m:6 word)
                                                              3) (word 1))
                                         (word_and (word_ushr (word m) 4)
                                                   (word 1)))
                               (word_ushr (word m) 5))):int16 =
           iword(&(m MOD 2 + (m DIV 2) MOD 2 + (m DIV 4) MOD 2) -
                 &((m DIV 8) MOD 2 + (m DIV 16) MOD 2 + (m DIV 32) MOD 2))`;;

let CBD3_FIELD = assume_spec CBD3_FIELD_STMT;;

let CBD3_LANE_STMT =
  `!n i j w:24 word.
      j < 4 /\ word(n DIV 2 EXP (24 * i)) = w
      ==> let x:6 word = word_subword w (6 * j,6) in
          word_sub
            (word_zx (word_add (word_add (word_and x (word 1))
                                         (word_and (word_ushr x 1) (word 1)))
                               (word_and (word_ushr x 2) (word 1))))
            (word_zx (word_add (word_add (word_and (word_ushr x 3) (word 1))
                                         (word_and (word_ushr x 4) (word 1)))
                               (word_ushr x 5))):int16 =
          iword(&((n DIV 2 EXP (6 * (4 * i + j))) MOD 2 +
                  (n DIV 2 EXP (6 * (4 * i + j) + 1)) MOD 2 +
                  (n DIV 2 EXP (6 * (4 * i + j) + 2)) MOD 2) -
                &((n DIV 2 EXP (6 * (4 * i + j) + 3)) MOD 2 +
                  (n DIV 2 EXP (6 * (4 * i + j) + 4)) MOD 2 +
                  (n DIV 2 EXP (6 * (4 * i + j) + 5)) MOD 2))`;;

let CBD3_LANE = assume_spec CBD3_LANE_STMT;;

let CBD3_LANE_RULE tth th =
  let addr = rand(rand(rand(rator(lhand(concl th))))) in
  let j = match addr with
      Comb(Comb(Const("word_add",_),Comb(Comb(Const("word_add",_),_),_)),
           Comb(Const("word",_),k)) -> dest_small_numeral k / 2
    | _ -> 0 in
  let jt = mk_small_numeral j in
  let lth = CONV_RULE(TOP_DEPTH_CONV let_CONV THENC
                      ONCE_DEPTH_CONV NUM_MULT_CONV THENC
                      REWRITE_CONV[ADD_CLAUSES])
   (MP (SPECL [`n:num`; `i:num`; jt; `w:24 word`] CBD3_LANE)
       (CONJ (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool` jt `4`)))
             tth)) in
  let eq = mk_eq(rand(concl th),lhs(concl lth)) in
  CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]))
   (TRANS th (TRANS (BITBLAST_RULE eq) lth));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_cbd 3 in common/fips203.ml, coefficient i *)
(* of the result is the number of 1 bits among bits 6 * i to 6 * i + 2 of    *)
(* the 192 bytes as a number n, minus the number among bits 6 * i + 3 to     *)
(* 6 * i + 5, here as a 16-bit integer rather than modulo 3329.              *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_CBD3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a n pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,512)) [(word pc,libmlkem_size); (a,192)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + mlkem_poly_cbd3) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,192)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          iword(&((n DIV 2 EXP (6 * i)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 1)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 2)) MOD 2) -
                                &((n DIV 2 EXP (6 * i + 3)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 4)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 5)) MOD 2)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_CBD3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_CBD3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_poly_cbd3_signature =
  ([("r", "int16_t[static 256]", "false");
    ("a", "uint8_t[static 192]", "true")],
   "void",
   [("a", "192", 1)],
   [("r", "256", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word(pc + mlkem_poly_cbd3_const1):int64`,`32`]
    ~keep_maychanges:true
    mlkem_native_poly_cbd3_signature
    MLKEM_NATIVE_POLY_CBD3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_CBD3_GCC12_O2_EXEC;;

let MLKEM_NATIVE_POLY_CBD3_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; a,192]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                    read PC s = word (pc + mlkem_poly_cbd3) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2
                         [a,192; r,512; word (pc + mlkem_poly_cbd3_consts),32]
                         [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (r,512)])`;;

let MLKEM_NATIVE_POLY_CBD3_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_CBD3_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
