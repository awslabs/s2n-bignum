(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of a 32-byte message to a polynomial. This is the code for     *)
(* mlkem_poly_frommsg from mlkem-native's portable C implementation compiled *)
(* by clang 17 with -O3 (see mlkem_native/README.md), where the inner loop   *)
(* over the bits of a byte is unrolled. It is verified in the whole image    *)
(* (see libmlkem.ml).                                                        *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image, where the pattern of +0x18 to +0x2c is repeated
 *** for the other bits, with the mask in w12 and the stores at offsets -6,
 *** -4, -2, 0, 2 and 4 from x9:

    mlkem_poly_frommsg:
       +0x0: mov     x8, xzr
       +0x4: add     x9, x0, #0x8
       +0x8: mov     w10, #0x681
       +0xc: mov     w11, #0x1
      +0x10: ldrb    w12, [x1, x8]
      +0x14: and     w11, w11, w12
      +0x18: mov     w12, #0x2
      +0x1c: neg     w11, w11
      +0x20: and     w11, w10, w11, lsr #16
      +0x24: sturh   w11, [x9, #-8]
      +0x28: ldrb    w11, [x1, x8]
      +0x2c: and     w11, w12, w11
      ...
      +0xb8: ldrb    w11, [x1, x8]
      +0xbc: add     x8, x8, #0x1
      +0xc0: cmp     x8, #0x20
      +0xc4: and     w11, w12, w11
      +0xc8: neg     w11, w11
      +0xcc: and     w11, w10, w11, lsr #16
      +0xd0: strh    w11, [x9, #6]
      +0xd4: add     x9, x9, #0x10
      +0xd8: b.ne    <mlkem_poly_frommsg+0xc>
      +0xdc: ret
 ***)

let MLKEM_NATIVE_POLY_FROMMSG_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_poly_frommsg"];;

(* ------------------------------------------------------------------------- *)
(* The bits of a byte of an array given as a number.                         *)
(* ------------------------------------------------------------------------- *)

let BYTE_BIT_STMT =
  `!n m k. k < 8
           ==> (n DIV 2 EXP (m + k)) MOD 2 =
               (((n DIV 2 EXP m) MOD 256) DIV 2 EXP k) MOD 2`;;

let BYTE_BIT = assume_spec BYTE_BIT_STMT;;

(* ------------------------------------------------------------------------- *)
(* The stores are at offsets from -8 to 6 from x9, which is 16 * i + 8 bytes *)
(* after r in iteration i. So that the simulation can tell that the stores   *)
(* at negative offsets are inside the output, x9 is given in the invariants  *)
(* as word_sub (word_add r (word(16 * i + 16))) (word 8), and the addresses  *)
(* that the simulation produces from it are put in the form                  *)
(* word_add r (word(16 * i + k)) for 0 <= k < 16 before they are used: in    *)
(* the state, word_add r (word_sub (word(16 * i + 16)) (word c)), by         *)
(* FROMMSG_ADDR_CONV, and in the events, by FROMMSG_EVENT_ADDR_CONV.         *)
(* ------------------------------------------------------------------------- *)

let FROMMSG_ADDR_STMT =
  `!i c. c <= 16
         ==> word_sub (word (16 * i + 16)) (word c):int64 =
             word(16 * i + (16 - c))`;;

let FROMMSG_ADDR = assume_spec FROMMSG_ADDR_STMT;;

let FROMMSG_ADDR_CONV t =
  let th = PART_MATCH (lhand o rand) FROMMSG_ADDR t in
  let th' = MP th (EQT_ELIM(NUM_LE_CONV (lhand(concl th)))) in
  CONV_RULE (RAND_CONV(RAND_CONV(RAND_CONV NUM_SUB_CONV))) th';;

let FROMMSG_EVENT_ADDR_CONV =
  let pat1 =
    `word_add (word_sub (word_add r (word (16 * i + 16))) (word 8))
              (word c):int64`
  and pat2 = `word_sub (word_add r (word (16 * i + 16))) (word 8):int64`
  and rv,iv,cv,kv = `r:int64`,`i:num`,`c:num`,`k:num`
  and two63 = Num.power_num (Num.num_of_int 2) (Num.num_of_int 63)
  and two64 = Num.power_num (Num.num_of_int 2) (Num.num_of_int 64) in
  fun t ->
    let ins,k,negths =
      try let ins = term_match [] pat1 t in
          let c = dest_numeral (instantiate ins cv) in
          let k = Num.mod_num (Num.add_num (Num.num_of_int 8) c) two64 in
          let negths =
            if Num.lt_num c two63 then [] else
            [SYM(WORD_REDUCE_CONV
              (mk_comb(`word_neg:int64->int64`,
                       mk_comb(`word:num->int64`,
                               mk_numeral(Num.sub_num two64 c)))))] in
          ins,k,negths
      with Failure _ -> term_match [] pat2 t,Num.num_of_int 8,[] in
    let rhs = subst [instantiate ins rv,rv; instantiate ins iv,iv;
                     mk_numeral k,kv]
               `word_add r (word(16 * i + k)):int64` in
    prove(mk_eq(t,rhs),
          REWRITE_TAC negths THEN REWRITE_TAC[WORD_ADD] THEN
          CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_decompress 1 in common/fips203.ml, the    *)
(* result for a bit y is the integer closest to 3329 * y / 2, rounding up on *)
(* ties, i.e. (3329 * y + 1) DIV 2.                                          *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_FROMMSG_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a n pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,512)) [(word pc,libmlkem_size); (a,32)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem_poly_frommsg) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,32)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP i) MOD 2 + 1) DIV 2))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_FROMMSG_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_FROMMSG_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_poly_frommsg_signature =
  ([("r", "int16_t[static 256]", "false");
    ("a", "uint8_t[static 32]", "true")],
   "void",
   [("a", "32", 1)],
   [("r", "256", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    mlkem_native_poly_frommsg_signature
    MLKEM_NATIVE_POLY_FROMMSG_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_FROMMSG_CLANG17_O3_EXEC;;

let MLKEM_NATIVE_POLY_FROMMSG_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; a,32]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem_poly_frommsg) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2 [a,32; r,512] [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (r,512)])`;;

let MLKEM_NATIVE_POLY_FROMMSG_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_FROMMSG_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
