(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Scalar product of 2-element polynomial vectors in NTT domain. This is     *)
(* the code for mlk_polyvec_basemul_acc_montgomery_cached_c512 from          *)
(* mlkem-native's portable C implementation compiled by gcc 12 with -O2 as   *)
(* one translation unit (see mlkem_native/README.md), which is the same as   *)
(* mlkem512_polyvec_basemul_acc_montgomery_cached of the separate -O2        *)
(* build. It is verified in the whole image (see libmlkem.ml), with the      *)
(* proof for the separate -O2 build adapted to the image.                    *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/libmlkem.ml";;

(*** The code in the image:

    mlk_polyvec_basemul_acc_montgomery_cached_c512:
       +0x0: mov     x4, x1
       +0x4: mov     x7, x0
       +0x8: mov     x5, x2
       +0xc: mov     x6, x3
      +0x10: add     x13, x1, #0x200
      +0x14: mov     w12, #0xfffff301
      +0x18: mov     w11, #0xfffff2ff
      +0x1c: nop
      +0x20: ldrsh   w16, [x4, #2]
      +0x24: add     x4, x4, #0x4
      +0x28: ldrsh   w0, [x5]
      +0x2c: add     x6, x6, #0x2
      +0x30: ldrsh   w1, [x5, #512]
      +0x34: add     x7, x7, #0x4
      +0x38: ldursh  w10, [x4, #-4]
      +0x3c: add     x5, x5, #0x4
      +0x40: ldrsh   w15, [x4, #510]
      +0x44: ldrsh   w14, [x4, #508]
      +0x48: ldursh  w3, [x6, #-2]
      +0x4c: ldrsh   w9, [x6, #254]
      +0x50: mul     w18, w10, w0
      +0x54: ldrsh   w2, [x5, #510]
      +0x58: mul     w0, w16, w0
      +0x5c: ldursh  w8, [x5, #-2]
      +0x60: mul     w17, w14, w1
      +0x64: mul     w1, w15, w1
      +0x68: madd    w3, w3, w16, w18
      +0x6c: madd    w2, w2, w14, w1
      +0x70: madd    w0, w8, w10, w0
      +0x74: madd    w9, w9, w15, w17
      +0x78: add     w2, w2, w0
      +0x7c: add     w3, w3, w9
      +0x80: mul     w0, w2, w12
      +0x84: mul     w1, w3, w12
      +0x88: sxth    w0, w0
      +0x8c: sxth    w1, w1
      +0x90: madd    w0, w0, w11, w2
      +0x94: madd    w1, w1, w11, w3
      +0x98: asr     w0, w0, #16
      +0x9c: sturh   w0, [x7, #-2]
      +0xa0: asr     w1, w1, #16
      +0xa4: sturh   w1, [x7, #-4]
      +0xa8: cmp     x4, x13
      +0xac: b.ne    <mlk_polyvec_basemul_acc_montgomery_cached_c512+0x20>
      +0xb0: ret
 ***)

let MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_MONO_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mono_mc
   [layout_range "mlk_polyvec_basemul_acc_montgomery_cached_c512"];;

(* ------------------------------------------------------------------------- *)
(* Definitions used to state specification, as for mlkem_basemul_k2.         *)
(* ------------------------------------------------------------------------- *)

let pmull = define
  `pmull (x0: int) (x1 : int) (y0 : int) (y1 : int) = x1 * y1 + x0 * y0`;;

let pmull_acc2 = define
    `pmull_acc2 (x00: int) (x01 : int) (y00 : int) (y01 : int)
          (x10: int) (x11 : int) (y10 : int) (y11 : int) =
      pmull x10 x11 y10 y11 + pmull x00 x01 y00 y01`;;

let pmul_acc2 = define
    `pmul_acc2 (x00: int) (x01 : int) (y00 : int) (y01 : int)
          (x10: int) (x11 : int) (y10 : int) (y11 : int) =
     (&(inverse_mod 3329 65536) *
      pmull_acc2 x00 x01 y00 y01 x10 x11 y10 y11) rem &3329`;;

let basemul2_even = define
   `basemul2_even x0 y0 y0t x1 y1 y1t = \i.
      pmul_acc2 (x0 (2 * i)) (x0 (2 * i + 1))
                (y0 (2 * i)) (y0t i)
                (x1 (2 * i)) (x1 (2 * i + 1))
                (y1 (2 * i)) (y1t i)`;;

let basemul2_odd = define
 `basemul2_odd x0 y0 x1 y1 = \i.
    pmul_acc2 (x0 (2 * i)) (x0 (2 * i + 1))
              (y0 (2 * i + 1)) (y0 (2 * i))
              (x1 (2 * i)) (x1 (2 * i + 1))
              (y1 (2 * i + 1)) (y1 (2 * i))`;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BASEMUL_ADDR_NORM_RULES =
  map ARITH_RULE
   [`2 * 2 * i = 4 * i`; `2 * (2 * i + 1) = 4 * i + 2`;
    `512 + 2 * 2 * i = 4 * i + 512`; `512 + 2 * (2 * i + 1) = 4 * i + 514`;
    `256 + 2 * i = 2 * i + 256`];;

(*** Instantiate a quantified input fact at a particular index ***)

let SPECIALIZE_LOAD_TAC (f,idx) =
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && free_in f (concl th) then
      MP_TAC(SPEC idx th) else failwith "SPECIALIZE_LOAD_TAC") THEN
  ANTS_TAC THENL
   [ASM_ARITH_TAC;
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE BASEMUL_ADDR_NORM_RULES)];;

(*** Prove the congruence for a Montgomery-reduced sum of products ***)

let MONTRED_SCALAR_CONG_TAC =
  ASSUM_LIST(fun ths -> W(fun (asl,w) ->
    let tm = rand(rand(lhand(rator w))) in
    let th1 = WEAKEN_INTCONG_RULE (num 3329) (GEN_CONGBOUND_RULE ths tm) in
    let th2 = MATCH_MP CONGBOUND_MONTRED_SCALAR th1 in
    let th3 = MP th2 (EQT_ELIM(INT_REDUCE_CONV(lhand(concl th2)))) in
    MP_TAC(CONJUNCT1 th3))) THEN
  REWRITE_TAC[basemul2_even; basemul2_odd;
              pmul_acc2; pmull_acc2; pmull; o_THM] THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC INT_RING;;

(*** Unlike mlkem_basemul_k2, this uses X18 as a temporary register ***)

let MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_MONO_CORRECT = prove
 (`!srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t pc.
     aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
     ALL (nonoverlapping (dst, 512))
         [(word pc,libmlkem_size); (srcA, 1024); (srcB, 1024); (srcBt, 512)]
     ==>
     ensures arm
       (\s. aligned_bytes_loaded s (word pc)
              mlkem_native_libmlkem_gcc12_O2_mono_mc /\
            read PC s = word (pc + mlk_polyvec_basemul_acc_montgomery_cached_c512) /\
            C_ARGUMENTS [dst; srcA; srcB; srcBt] s  /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (2 * i)))) s = x0 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB  (word (2 * i)))) s = y0 i) /\
            (!i. i < 128
                 ==> read(memory :> bytes16
                      (word_add srcBt (word (2 * i)))) s = y0t i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (512 + 2 * i)))) s = x1 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB (word (512 + 2 * i)))) s = y1 i) /\
            (!i. i < 128
                 ==> read(memory :> bytes16
                      (word_add srcBt (word (256 + 2 * i)))) s = y1t i))
       (\s. read PC s = word (pc + mlk_polyvec_basemul_acc_montgomery_cached_c512_ret) /\
            ((!i. i < 256
                  ==> abs(ival(x0 i)) <= &2 pow 12 /\
                      abs(ival(x1 i)) <= &2 pow 12)
             ==> (!i. i < 128
                      ==> (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i)))) s) ==
                           basemul2_even (ival o x0) (ival o y0) (ival o y0t)
                                         (ival o x1) (ival o y1) (ival o y1t)
                                         i) (mod &3329) /\
                          (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i + 2)))) s) ==
                           basemul2_odd (ival o x0) (ival o y0) (ival o x1)
                           (ival o y1) i) (mod &3329))))
       (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                   X12; X13; X14; X15; X16; X17; X18] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
        MAYCHANGE [memory :> bytes(dst, 512)])`,
  MAP_EVERY X_GEN_TAC
   [`srcA:int64`; `srcB:int64`; `srcBt:int64`; `dst:int64`;
    `x0:num->int16`; `y0:num->int16`; `y0t:num->int16`;
    `x1:num->int16`; `y1:num->int16`; `y1t:num->int16`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `128` `pc + mlk_polyvec_basemul_acc_montgomery_cached_c512_loop1`
   `pc + mlk_polyvec_basemul_acc_montgomery_cached_c512_loop1_test`
   `\i s. read X4 s = word_add srcA (word(4 * i)) /\
          read X5 s = word_add srcB (word(4 * i)) /\
          read X6 s = word_add srcBt (word(2 * i)) /\
          read X7 s = word_add dst (word(4 * i)) /\
          read X13 s = word_add srcA (word 512) /\
          read X12 s = word 4294963969 /\ read X11 s = word 4294963967 /\
          (!i. i < 256
               ==> read(memory :> bytes16
                    (word_add srcA (word (2 * i)))) s = x0 i) /\
          (!i. i < 256
               ==> read(memory :> bytes16
                    (word_add srcB  (word (2 * i)))) s = y0 i) /\
          (!i. i < 128
               ==> read(memory :> bytes16
                    (word_add srcBt (word (2 * i)))) s = y0t i) /\
          (!i. i < 256
               ==> read(memory :> bytes16
                    (word_add srcA (word (512 + 2 * i)))) s = x1 i) /\
          (!i. i < 256
               ==> read(memory :> bytes16
                    (word_add srcB (word (512 + 2 * i)))) s = y1 i) /\
          (!i. i < 128
               ==> read(memory :> bytes16
                    (word_add srcBt (word (256 + 2 * i)))) s = y1t i) /\
          ((!i. i < 256
                ==> abs(ival(x0 i)) <= &2 pow 12 /\
                    abs(ival(x1 i)) <= &2 pow 12)
           ==> (!j. j < i
                    ==> (ival(read(memory :> bytes16
                           (word_add dst (word (4 * j)))) s) ==
                         basemul2_even (ival o x0) (ival o y0) (ival o y0t)
                                       (ival o x1) (ival o y1) (ival o y1t)
                                       j) (mod &3329) /\
                        (ival(read(memory :> bytes16
                           (word_add dst (word (4 * j + 2)))) s) ==
                         basemul2_odd (ival o x0) (ival o y0) (ival o x1)
                         (ival o y1) j) (mod &3329)))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization of pointers and constants ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_MONO_EXEC (1--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; CONJUNCT1 LT];

    (*** The loop body, computing two output coefficients ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY SPECIALIZE_LOAD_TAC
     [`x0:num->int16`,`2 * i`; `x0:num->int16`,`2 * i + 1`;
      `x1:num->int16`,`2 * i`; `x1:num->int16`,`2 * i + 1`;
      `y0:num->int16`,`2 * i`; `y0:num->int16`,`2 * i + 1`;
      `y1:num->int16`,`2 * i`; `y1:num->int16`,`2 * i + 1`;
      `y0t:num->int16`,`i:num`; `y1t:num->int16`,`i:num`] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_MONO_EXEC (1--34) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`;
                  ARITH_RULE `2 * (i + 1) = 2 * i + 2`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC]) THEN
    DISCH_TAC THEN X_GEN_TAC `j:num` THEN
    REWRITE_TAC[ARITH_RULE `j < i + 1 <=> j < i \/ j = i`] THEN
    STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MLKEM_NATIVE_W_SIMP_TAC THEN
    REWRITE_TAC[WORD_ADD_0] THEN REWRITE_TAC[GSYM montred_scalar] THEN
    SUBGOAL_THEN
     `abs(ival(x0(2 * i):int16)) <= &2 pow 12 /\
      abs(ival(x1(2 * i):int16)) <= &2 pow 12 /\
      abs(ival(x0(2 * i + 1):int16)) <= &2 pow 12 /\
      abs(ival(x1(2 * i + 1):int16)) <= &2 pow 12`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `i < 128 ==> 2 * i < 256 /\ 2 * i + 1 < 256`];
      ALL_TAC] THEN
    CONJ_TAC THEN MONTRED_SCALAR_CONG_TAC;

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_MONO_EXEC (1--2) THEN
    SUBGOAL_THEN
     `~(val(word_sub (word_add srcA (word (4 * i)))
                     (word_add srcA (word 512)):int64) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[WORD_RULE
       `word_sub (word_add a x) (word_add a y) = word_sub x y`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 128 ==> 4 * i < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_MONO_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

let MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT = prove
 (`!srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t pc returnaddress.
     aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
     ALL (nonoverlapping (dst, 512))
         [(word pc,libmlkem_size); (srcA, 1024); (srcB, 1024); (srcBt, 512)]
     ==>
     ensures arm
       (\s. aligned_bytes_loaded s (word pc)
              mlkem_native_libmlkem_gcc12_O2_mono_mc /\
            read PC s = word (pc + mlk_polyvec_basemul_acc_montgomery_cached_c512) /\
            read X30 s = returnaddress /\
            C_ARGUMENTS [dst; srcA; srcB; srcBt] s  /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (2 * i)))) s = x0 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB  (word (2 * i)))) s = y0 i) /\
            (!i. i < 128
                 ==> read(memory :> bytes16
                      (word_add srcBt (word (2 * i)))) s = y0t i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (512 + 2 * i)))) s = x1 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB (word (512 + 2 * i)))) s = y1 i) /\
            (!i. i < 128
                 ==> read(memory :> bytes16
                      (word_add srcBt (word (256 + 2 * i)))) s = y1t i))
       (\s. read PC s = returnaddress /\
            ((!i. i < 256
                  ==> abs(ival(x0 i)) <= &2 pow 12 /\
                      abs(ival(x1 i)) <= &2 pow 12)
             ==> (!i. i < 128
                      ==> (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i)))) s) ==
                           basemul2_even (ival o x0) (ival o y0) (ival o y0t)
                                         (ival o x1) (ival o y1) (ival o y1t)
                                         i) (mod &3329) /\
                          (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i + 2)))) s) ==
                           basemul2_odd (ival o x0) (ival o y0) (ival o x1)
                           (ival o y1) i) (mod &3329))))
       (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                   X12; X13; X14; X15; X16; X17; X18] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
        MAYCHANGE [memory :> bytes(dst, 512)])`,
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_MONO_EXEC
    MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_MONO_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The C signature is the same as that of mlkem_basemul_k2 ***)

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_basemul_k2" subroutine_signatures)
    MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_MONO_EXEC;;

let MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e srcA srcB srcBt dst pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (dst,512))
           [word pc,libmlkem_size; srcA,1024; srcB,1024; srcBt,512]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                    read PC s = word (pc + mlk_polyvec_basemul_acc_montgomery_cached_c512) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [dst; srcA; srcB; srcBt] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events srcA srcB srcBt dst pc returnaddress /\
                        memaccess_inbounds e2
                         [srcA,1024; srcB,1024; srcBt,512; dst,512]
                         [dst,512])
               (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                           X11; X12; X13; X14; X15; X16; X17; X18] ,,
                MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
                MAYCHANGE [memory :> bytes(dst, 512)])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(srcA:int64) (srcB:int64) (srcBt:int64) (dst:int64) (pc:num)
      (returnaddress:int64).
      APPEND
        (f_ev_epil srcA srcB srcBt dst pc returnaddress)
        (APPEND
          (ENUMERATEL 128
            (\i. f_ev_loop srcA srcB srcBt dst pc returnaddress i))
          (f_ev_prol srcA srcB srcBt dst pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              SOME_FLAGS; ALL;
              fst MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_MONO_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `128` `pc + mlk_polyvec_basemul_acc_montgomery_cached_c512_loop1`
   `pc + mlk_polyvec_basemul_acc_montgomery_cached_c512_loop1_exit`
    `\i s. read X30 s = returnaddress /\
           read X4 s = word_add srcA (word(4 * i)) /\
           read X5 s = word_add srcB (word(4 * i)) /\
           read X6 s = word_add srcBt (word(2 * i)) /\
           read X7 s = word_add dst (word(4 * i)) /\
           read X13 s = word_add srcA (word 512)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false
        MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_MONO_EXEC (1--8) THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_MONO_EXEC (1--1) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_MONO_EXEC (1--36) THEN
  SUBGOAL_THEN
   `~(val(word_sub (word_add (word_add srcA (word (4 * i))) (word 4))
                   (word_add srcA (word 512)):int64) = 0) <=>
    i + 1 < 128`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[WORD_RULE
     `word_sub (word_add (word_add a y) z) (word_add a x):int64 =
      word_sub (word_add y z) x`] THEN
    REWRITE_TAC[VAL_WORD_SUB_EQ_0; GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 128 ==> 4 * i + 4 < 18446744073709551616`] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`;
                ARITH_RULE `2 * (i + 1) = 2 * i + 2`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC]) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The same code in the whole image (see libmlkem.ml).                       *)
(* ------------------------------------------------------------------------- *)

