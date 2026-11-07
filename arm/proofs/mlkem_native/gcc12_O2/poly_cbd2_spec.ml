(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling of a polynomial from the centered binomial distribution with eta *)
(* = 2. This is the code for mlkem_poly_cbd2 from mlkem-native's portable C  *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md),  *)
(* which the compiler has partly vectorized. It is verified in the whole     *)
(* image (see libmlkem.ml), with vectors of shift                            *)
(* amounts.                                                                  *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_cbd2:
       +0x0: mov     x5, x0
       +0x4: adrp    x0, <page>
       +0x8: adrp    x2, <page>
       +0xc: mov     x4, x1
      +0x10: ldr     q7, [x0, #608]
      +0x14: adrp    x0, <page>
      +0x18: ldr     q16, [x2, #592]
      +0x1c: mov     x1, #0x0
      +0x20: ldr     q6, [x0, #624]
      +0x24: adrp    x0, <page>
      +0x28: movi    v3.8h, #0x3
      +0x2c: ldr     q5, [x0, #640]
      +0x30: lsl     x2, x1, #4
      +0x34: ldr     w0, [x4, x1, lsl #2]
      +0x38: add     x1, x1, #0x1
      +0x3c: and     w3, w0, #0x55555555
      +0x40: lsr     w0, w0, #1
      +0x44: and     w0, w0, #0x55555555
      +0x48: add     w0, w0, w3
      +0x4c: dup     v0.4s, w0
      +0x50: ushl    v1.4s, v0.4s, v16.4s
      +0x54: ushl    v4.4s, v0.4s, v7.4s
      +0x58: ushl    v2.4s, v0.4s, v6.4s
      +0x5c: ushl    v0.4s, v0.4s, v5.4s
      +0x60: uzp1    v1.8h, v1.8h, v4.8h
      +0x64: uzp1    v2.8h, v2.8h, v0.8h
      +0x68: and     v0.16b, v1.16b, v3.16b
      +0x6c: and     v1.16b, v2.16b, v3.16b
      +0x70: sub     v0.8h, v0.8h, v1.8h
      +0x74: str     q0, [x5, x2]
      +0x78: cmp     x1, #0x20
      +0x7c: b.ne    <mlkem_poly_cbd2+0x30>
      +0x80: ret
 ***)

let MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [layout_range "mlkem_poly_cbd2"];;

(*** The vectors of 32-bit shifts, negative for right shifts ***)

let MLKEM_NATIVE_POLY_CBD2_GCC12_O2_CONSTANTS =
  map (fun d -> MLKEM_NATIVE_IMAGE_CONST_RULE d 128)
      [layout "mlkem_poly_cbd2_const1"; layout "mlkem_poly_cbd2_const2";
       layout "mlkem_poly_cbd2_const3"; layout "mlkem_poly_cbd2_const4"];;

(* ------------------------------------------------------------------------- *)
(* Each iteration loads a 32-bit word t of the input and adds its pairs of   *)
(* bits. Coefficient j of 8 is computed from the sum shifted right by 4 * j  *)
(* and 4 * j + 2, which depends only on the 4-bit field j of t. Below, the   *)
(* computation on a 4-bit field is checked for all its values and related    *)
(* to the bits of the number for the input bytes.                            *)
(* ------------------------------------------------------------------------- *)

let NIBBLE_BIT_STMT =
  `!n m k. k < 4
           ==> (n DIV 2 EXP (m + k)) MOD 2 =
               (((n DIV 2 EXP m) MOD 16) DIV 2 EXP k) MOD 2`;;

let NIBBLE_BIT = assume_spec NIBBLE_BIT_STMT;;

let CBD2_NIBBLE_STMT =
  `!m. m < 16
       ==> word_sub
            (word_zx (word_add (word_and (word m:4 word) (word 1))
                               (word_and (word_ushr (word m) 1) (word 1))))
            (word_zx (word_add (word_and (word_ushr (word m:4 word) 2)
                                         (word 1))
                               (word_ushr (word m) 3))):int16 =
           iword(&(m MOD 2 + (m DIV 2) MOD 2) -
                 &((m DIV 4) MOD 2 + (m DIV 8) MOD 2))`;;

let CBD2_NIBBLE = assume_spec CBD2_NIBBLE_STMT;;

let CBD2_LANE_STMT =
  `!n i j t:int32.
      j < 8 /\ word((n DIV 2 EXP (32 * i)) MOD 4294967296) = t
      ==> let x:4 word = word_subword t (4 * j,4) in
          word_sub
            (word_zx (word_add (word_and x (word 1))
                               (word_and (word_ushr x 1) (word 1))))
            (word_zx (word_add (word_and (word_ushr x 2) (word 1))
                               (word_ushr x 3))):int16 =
          iword(&((n DIV 2 EXP (4 * (8 * i + j))) MOD 2 +
                  (n DIV 2 EXP (4 * (8 * i + j) + 1)) MOD 2) -
                &((n DIV 2 EXP (4 * (8 * i + j) + 2)) MOD 2 +
                  (n DIV 2 EXP (4 * (8 * i + j) + 3)) MOD 2))`;;

let CBD2_LANE = assume_spec CBD2_LANE_STMT;;

(*** Lane j of the 128-bit store, for t as given by tth ***)

let CBD2_LANE_RULE tth th =
  let addr = rand(rand(rand(rator(lhand(concl th))))) in
  let j = match addr with
      Comb(Comb(Const("word_add",_),Comb(Comb(Const("word_add",_),_),_)),
           Comb(Const("word",_),k)) -> dest_small_numeral k / 2
    | _ -> 0 in
  let jt = mk_small_numeral j in
  let lth = CONV_RULE(TOP_DEPTH_CONV let_CONV THENC
                      ONCE_DEPTH_CONV NUM_MULT_CONV THENC
                      REWRITE_CONV[ADD_CLAUSES])
   (MP (SPECL [`n:num`; `i:num`; jt; `t:int32`] CBD2_LANE)
       (CONJ (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool` jt `8`)))
             tth)) in
  let eq = mk_eq(rand(concl th),lhs(concl lth)) in
  CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]))
   (TRANS th (TRANS (BITBLAST_RULE eq) lth));;

(*** The first step of the loop body, normalizing the offset 16 * i ***)

let CBD2_INDEX_TAC =
  SUBGOAL_THEN `val(word i:int64) = i` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `i < 32` THEN ARITH_TAC; ALL_TAC] THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC [1] THEN
  FIRST_X_ASSUM(ASSUME_TAC o
    CONV_RULE(RAND_CONV(REWRITE_CONV[WORD_SHL_WORD] THENC
                        ONCE_DEPTH_CONV NUM_REDUCE_CONV)) o
    check (can (term_match [] `read X2 s = x`) o concl));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_cbd 2 in common/fips203.ml, coefficient i *)
(* of the result is the number of 1 bits among bits 4 * i and 4 * i + 1 of   *)
(* the 128 bytes as a number n, minus the number among bits 4 * i + 2 and    *)
(* 4 * i + 3, here as a 16-bit integer rather than modulo 3329.              *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_CBD2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a n pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,512)) [(word pc,libmlkem_size); (a,128)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + mlkem_poly_cbd2) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,128)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          iword(&((n DIV 2 EXP (4 * i)) MOD 2 +
                                  (n DIV 2 EXP (4 * i + 1)) MOD 2) -
                                &((n DIV 2 EXP (4 * i + 2)) MOD 2 +
                                  (n DIV 2 EXP (4 * i + 3)) MOD 2)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_CBD2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_CBD2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_poly_cbd2_signature =
  ([("r", "int16_t[static 256]", "false");
    ("a", "uint8_t[static 128]", "true")],
   "void",
   [("a", "128", 1)],
   [("r", "256", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word(pc + mlkem_poly_cbd2_const1):int64`,`64`]
    ~keep_maychanges:true
    mlkem_native_poly_cbd2_signature
    MLKEM_NATIVE_POLY_CBD2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC;;

let MLKEM_NATIVE_POLY_CBD2_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; a,128]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                    read PC s = word (pc + mlkem_poly_cbd2) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2
                         [a,128; r,512; word (pc + mlkem_poly_cbd2_consts),64]
                         [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (r,512)])`;;

let MLKEM_NATIVE_POLY_CBD2_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_CBD2_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
