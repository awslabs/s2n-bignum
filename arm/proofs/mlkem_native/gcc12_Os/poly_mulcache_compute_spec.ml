(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Precomputation of the mulcache for polynomial multiplication.             *)
(* This is the code for mlkem_poly_mulcache_compute from mlkem-native's      *)
(* portable C implementation compiled by gcc 12 with -Os (see               *)
(* mlkem_native/README.md). It is the scalar loop over the 64 pairs of       *)
(* outputs that -O2 produces, reading the zetas from the table mlk_zetas in  *)
(* the read-only data, but it steps the pointers to the input and the        *)
(* output before the loads and stores, with negative offsets. It is verified *)
(* in the whole image (see libmlkem.ml), with the same statements as the -O2 *)
(* code.                                                                     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_mulcache_compute:
       +0x0: add     x4, x1, #0x2
       +0x4: adrp    x5, <page>
       +0x8: add     x1, x1, #0x202
       +0xc: add     x5, x5, #0xb00
      +0x10: mov     w8, #0xfffff301
      +0x14: mov     w7, #0xfffff2ff
      +0x18: ldrsh   w3, [x5, #128]
      +0x1c: add     x4, x4, #0x8
      +0x20: ldursh  w6, [x4, #-8]
      +0x24: add     x5, x5, #0x2
      +0x28: add     x0, x0, #0x4
      +0x2c: mul     w6, w6, w3
      +0x30: neg     w3, w3
      +0x34: sxth    w3, w3
      +0x38: mul     w2, w6, w8
      +0x3c: sxth    w2, w2
      +0x40: madd    w2, w2, w7, w6
      +0x44: asr     w2, w2, #16
      +0x48: sturh   w2, [x0, #-4]
      +0x4c: ldursh  w2, [x4, #-4]
      +0x50: mul     w3, w2, w3
      +0x54: mul     w2, w3, w8
      +0x58: sxth    w2, w2
      +0x5c: madd    w2, w2, w7, w3
      +0x60: asr     w2, w2, #16
      +0x64: sturh   w2, [x0, #-2]
      +0x68: cmp     x1, x4
      +0x6c: b.ne    <mlkem_poly_mulcache_compute+0x18>
      +0x70: ret
 ***)

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_Os_mc
   [layout_range "mlkem_poly_mulcache_compute"];;

(*** The table of zetas in the image ***)

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_OS_ZETAS_IN_IMAGE =
  MLKEM_NATIVE_IMAGE_DATA_RULE mlk_zetas_data (layout "rodata_mlk_zetas");;

(* ------------------------------------------------------------------------- *)
(* Properties of the zetas (see utils/mlkem_native.ml for the table).        *)
(* ------------------------------------------------------------------------- *)

(*** The zetas used for the mulcache are those in the second half ***)

let MLK_ZETAS_MULCACHE_STMT =
  `!i. i < 64
       ==> abs(EL (64 + i) mlk_zetas) <= &1664 /\
           (&169 * EL (64 + i) mlk_zetas ==
            &17 pow (2 * bitreverse7 (2 * i) + 1)) (mod &3329) /\
           (&169 * --(EL (64 + i) mlk_zetas) ==
            &17 pow (2 * bitreverse7 (2 * i + 1) + 1)) (mod &3329)`;;

let MLK_ZETAS_MULCACHE = assume_spec MLK_ZETAS_MULCACHE_STMT;;

let MLK_ZETAS_MULCACHE_IVAL_STMT =
  `!i. i < 64
       ==> ival(iword(EL (64 + i) mlk_zetas):int16) = EL (64 + i) mlk_zetas /\
           abs(ival(iword(EL (64 + i) mlk_zetas):int16)) <= &1664 /\
           (&169 * ival(iword(EL (64 + i) mlk_zetas):int16) ==
            &17 pow (2 * bitreverse7 (2 * i) + 1)) (mod &3329) /\
           (&169 * --ival(iword(EL (64 + i) mlk_zetas):int16) ==
            &17 pow (2 * bitreverse7 (2 * i + 1) + 1)) (mod &3329)`;;

let MLK_ZETAS_MULCACHE_IVAL = assume_spec MLK_ZETAS_MULCACHE_IVAL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Some lemmas, tactics etc.                                                 *)
(* ------------------------------------------------------------------------- *)

let WORD_ZX_NEG_SX_STMT =
  `!z:int16. word_zx(word_sub (word 0) (word_sx z:int32)):int16 = word_neg z`;;

let WORD_ZX_NEG_SX = assume_spec WORD_ZX_NEG_SX_STMT;;

let CONG_MONT_ZETA = INTEGER_RULE
 `!n a z p x r:int. (r == a * (x * z)) (mod n) /\ (a * z == p) (mod n)
                    ==> (r == x * p) (mod n)`;;

let MULCACHE_ADDR_NORM_RULES =
  map ARITH_RULE
   [`2 * (64 + i) = 2 * i + 128`; `2 * (4 * i + 1) = 8 * i + 2`;
    `2 * (4 * i + 3) = 8 * i + 6`];;

(*** Instantiate a quantified input fact at a particular index ***)

let MSPEC_TAC (f,idx) =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_forall c &&
       (let b = snd(dest_forall c) in
        is_imp b && is_eq(rand b) && can (find_term ((=) f)) (rhs(rand b)))
    then MP_TAC(SPEC idx th) else failwith "MSPEC_TAC") THEN
  ANTS_TAC THENL
   [W(fun (asl,w) -> MP_TAC(ARITH_RULE (mk_imp(`i < 64`,w)))) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE MULCACHE_ADDR_NORM_RULES)];;

(*** Prove the result for one output coefficient ***)

let MULCACHE_OUTPUT_TAC =
  UNDISCH_THEN `i < 64` (fun th ->
    ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(MATCH_MP MLK_ZETAS_MULCACHE_IVAL th)) THEN
  ASSUM_LIST(fun ths -> W(fun (asl,w) ->
    let tm = rand(rand(lhand(rator(lhand w)))) in
    let th1 = WEAKEN_INTCONG_RULE (num 3329) (GEN_CONGBOUND_RULE ths tm) in
    let th2 = MATCH_MP CONGBOUND_MONTRED_SCALAR th1 in
    let th3 = CONV_RULE(ONCE_DEPTH_CONV INVERSE_MOD_CONV)
               (MP th2 (EQT_ELIM(INT_REDUCE_CONV(lhand(concl th2))))) in
    let cth,bth = CONJ_PAIR th3 in
    let zz = rand(rand(rand(rator(concl cth)))) in
    CONJ_TAC THENL
     [REWRITE_TAC[mulcache; o_THM; INT_CONG_RREM;
                  ARITH_RULE `2 * 2 * i + 1 = 4 * i + 1`;
                  ARITH_RULE `2 * (2 * i + 1) + 1 = 4 * i + 3`] THEN
      MATCH_MP_TAC CONG_MONT_ZETA THEN
      MAP_EVERY EXISTS_TAC [`&169:int`; zz] THEN
      CONJ_TAC THENL [ACCEPT_TAC cth; ASM_REWRITE_TAC[]];
      MP_TAC bth THEN CONV_TAC(LAND_CONV INT_REDUCE_CONV) THEN
      INT_ARITH_TAC]));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!dst src x pc returnaddress.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    ALL (nonoverlapping (dst,256)) [(word pc,libmlkem_size); (src,512)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_gcc12_Os_mc /\
           read PC s = word (pc + mlkem_poly_mulcache_compute) /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [dst; src] s /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add src (word (2 * i)))) s =
                    x i))
      (\s. read PC s = returnaddress /\
           !i. i < 128
               ==> let z_i = read(memory :> bytes16
                                (word_add dst (word (2 * i)))) s in
                   (ival z_i == (mulcache (ival o x)) i) (mod &3329) /\
                   abs(ival z_i) <= &3328)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(dst,256)])`;;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** Unlike mlkem_mulcache_compute, this has just two arguments, and the ***)
(*** table of zetas is a read-only object.                               ***)

let mlkem_native_poly_mulcache_compute_signature =
  ([("x", "int16_t[static 128]", "false");
    ("a", "int16_t[static 256]", "true")],
   "void",
   [("a", "256", 2)],
   [("x", "128", 2)],
   []);;
let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word(pc + rodata_mlk_zetas):int64`,`256`]
    ~keep_maychanges:true
    mlkem_native_poly_mulcache_compute_signature
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_OS_EXEC;;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e dst src pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (dst,256)) [word pc,libmlkem_size; src,512]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                     mlkem_native_libmlkem_gcc12_Os_mc /\
                    read PC s = word (pc + mlkem_poly_mulcache_compute) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [dst; src] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events src dst pc returnaddress /\
                        memaccess_inbounds e2
                         [src,512; dst,256; word (pc + rodata_mlk_zetas),256]
                         [dst,256])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(dst,256)])`;;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
