(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Centered binomial distribution with eta = 3. This is the code for         *)
(* mlkem_poly_cbd3 from mlkem-native's portable C implementation compiled by *)
(* gcc 12 with -Os (see mlkem_native/README.md). It is verified in the whole *)
(* image (see libmlkem.ml). The code is not vectorized: a loop over groups   *)
(* of three bytes adds the groups of three bits of the 24-bit word that they *)
(* make, and an inner loop over its 4 groups of 6 bits computes a            *)
(* coefficient each. The simulation unrolls the inner loop.                  *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_cbd3:
       +0x0: mov     w7, #0x9249
       +0x4: mov     w6, #0x0
       +0x8: movk    w7, #0x24, lsl #16
       +0xc: ldrb    w3, [x1, #2]
      +0x10: mov     w8, w6
      +0x14: ldrb    w2, [x1, #1]
      +0x18: ldrb    w4, [x1]
      +0x1c: lsl     w3, w3, #16
      +0x20: orr     w2, w3, w2, lsl #8
      +0x24: orr     w2, w2, w4
      +0x28: and     w4, w2, w7
      +0x2c: and     w3, w7, w2, lsr #1
      +0x30: and     w2, w7, w2, lsr #2
      +0x34: add     w2, w3, w2
      +0x38: mov     w3, #0x0
      +0x3c: add     w2, w2, w4
      +0x40: add     w5, w3, #0x3
      +0x44: lsr     w4, w2, w3
      +0x48: and     w4, w4, #0x7
      +0x4c: add     w3, w3, #0x6
      +0x50: lsr     w5, w2, w5
      +0x54: and     w5, w5, #0x7
      +0x58: sub     w4, w4, w5
      +0x5c: strh    w4, [x0, w8, uxtw #1]
      +0x60: add     w8, w8, #0x1
      +0x64: cmp     w3, #0x18
      +0x68: b.ne    <mlkem_poly_cbd3+0x40>
      +0x6c: add     w6, w6, #0x4
      +0x70: add     x1, x1, #0x3
      +0x74: cmp     w6, #0x100
      +0x78: b.ne    <mlkem_poly_cbd3+0xc>
      +0x7c: ret     
 ***)

let MLKEM_NATIVE_POLY_CBD3_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_Os_mc
   [layout_range "mlkem_poly_cbd3"];;

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

(*** Coefficient j of the 4 for the word w, as stored for the coefficient
 *** 4 * i + j: the computation is the same as for the lane j of the vector
 *** code, and bit-blasting shows that it is ***)

let CBD3_LANE_RULE j tth =
  let jt = mk_small_numeral j in
  let ct = if j = 0 then `4 * i` else
           mk_binop `(+):num->num->num` `4 * i` jt in
  let addr = mk_comb(mk_comb(`word_add:int64->int64->int64`,`r:int64`),
                     mk_comb(`word:num->int64`,
                             mk_binop `( * ):num->num->num` `2` ct)) in
  let pat = vsubst [addr,`addr:int64`] `read (memory :> bytes16 addr) s = x` in
  let lth = CONV_RULE(TOP_DEPTH_CONV let_CONV THENC
                      ONCE_DEPTH_CONV NUM_MULT_CONV THENC
                      REWRITE_CONV[ADD_CLAUSES])
   (MP (SPECL [`n:num`; `i:num`; jt; `w:24 word`] CBD3_LANE)
       (CONJ (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool` jt `4`)))
             tth)) in
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] pat) (concl th) then
      let th' = CONV_RULE(RAND_CONV(REWRITE_CONV[word_jushr; VAL_WORD; DIMINDEX_32]
                                    THENC NUM_REDUCE_CONV)) th in
      let eq = mk_eq(rand(concl th'),lhs(concl lth)) in
      ASSUME_TAC(TRANS th' (TRANS (BITBLAST_RULE eq) lth))
    else failwith "CBD3_LANE_RULE");;

(*** The index 4 * i + k of the coefficient, in X8, as an offset with UXTW ***)

let cbd3_indices = map (fun k ->
  if k = 0 then `4 * i` else
  mk_binop `(+):num->num->num` `4 * i` (mk_small_numeral k)) (0--3);;

let CBD3_INDEX_TAC k =
  let jt = el k cbd3_indices in
  let wt = mk_comb(`word:num->int64`,jt) in
  let zt = mk_comb(`word_zx:int32->int64`,
            mk_comb(`word_zx:int32->int32`,
             mk_comb(`word_zx:int64->int32`,wt))) in
  let zt2 = mk_comb(`word_zx:int32->int64`,
             mk_comb(`word_zx:int64->int32`,wt)) in
  let uxtw_tac tm =
    SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,tm),jt)) ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REPEAT MOD_LT_ASM_TAC THEN
      REWRITE_TAC[];
      ALL_TAC] in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read X8 s = x`) c then
      MP_TAC th THEN SUBGOAL_THEN (mk_eq(rand c,wt)) SUBST1_TAC THENL
       [WORD_SMALL_TAC; DISCH_TAC] THEN
      uxtw_tac zt THEN uxtw_tac zt2
    else failwith "CBD3_INDEX_TAC");;

(*** The 59 steps of an iteration of the outer loop, up to its test: the
 *** loads of the three bytes and the addition of the groups of three bits,
 *** four iterations of the inner loop of 11 instructions each, and the
 *** update of the pointers ***)

let CBD3_BODY_TAC =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_GCC12_OS_EXEC (1--2) THEN
  CBD3_INDEX_TAC 0 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_GCC12_OS_EXEC (3--13) THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_GCC12_OS_EXEC
     ((14 + 11 * k)--(22 + 11 * k)) THEN
    (if k < 3 then CBD3_INDEX_TAC (k + 1) else ALL_TAC) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_GCC12_OS_EXEC
     ((23 + 11 * k)--(24 + 11 * k))) (0--3) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_GCC12_OS_EXEC (58--59);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_cbd 3 in common/fips203/fips203.ml,       *)
(* coefficient i of the result is the number of 1 bits among bits 6 * i to 6 *)
(* * i + 2 of the 192 bytes as a number n, minus the number among bits 6 * i *)
(* + 3 to 6 * i + 5, here as a 16-bit integer rather than modulo 3329.       *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_CBD3_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a n pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,512)) [(word pc,libmlkem_size); (a,192)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_Os_mc /\
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

let MLKEM_NATIVE_POLY_CBD3_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_CBD3_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

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
    ~keep_maychanges:true
    mlkem_native_poly_cbd3_signature
    MLKEM_NATIVE_POLY_CBD3_GCC12_OS_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_CBD3_GCC12_OS_EXEC;;

let MLKEM_NATIVE_POLY_CBD3_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; a,192]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_Os_mc /\
                    read PC s = word (pc + mlkem_poly_cbd3) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2 [a,192; r,512] [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (r,512)])`;;

let MLKEM_NATIVE_POLY_CBD3_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_CBD3_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
