(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Scalar product of 4-element polynomial vectors in NTT domain.             *)
(* This is the code for mlkem1024_polyvec_basemul_acc_montgomery_cached      *)
(* from mlkem-native's portable C implementation compiled by gcc 12 with     *)
(* -O3 (see mlkem_native/README.md), verified in the whole image (see        *)
(* libmlkem.ml) with the specification of the -O2 code.                      *)
(*                                                                           *)
(* The code has the structure of the -O3 code for 2-element vectors (see     *)
(* basemul_k2.ml): a check for overlap of the output and the cache, which    *)
(* takes the vector loop when they do not overlap, and a loop that computes  *)
(* 8 pairs of outputs at a time from LD2 loads of the inputs. Since it uses  *)
(* D8 to D15, it saves them on the stack, with X19, X20 and X30, and it      *)
(* spills one vector to the stack in the loop, so unlike the -O2 code its    *)
(* specification has a stack frame of 128 bytes. The safety theorem also     *)
(* lists the vector of 3329^-1 mod 2^16 that the loop loads as read-only     *)
(* data.                                                                     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;

let MLKEM_NATIVE_BASEMUL_K4_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem1024_polyvec_basemul_acc_montgomery_cached"];;

(* ------------------------------------------------------------------------- *)
(* Definitions used to state specification, as for mlkem_basemul_k4.         *)
(* ------------------------------------------------------------------------- *)

let pmull = define
  `pmull (x0: int) (x1 : int) (y0 : int) (y1 : int) = x1 * y1 + x0 * y0`;;

let pmull_acc4 = define
  `pmull_acc4 (x00: int) (x01 : int) (y00 : int) (y01 : int)
              (x10: int) (x11 : int) (y10 : int) (y11 : int)
              (x20: int) (x21 : int) (y20 : int) (y21 : int)
              (x30: int) (x31 : int) (y30 : int) (y31 : int) =
              pmull x30 x31 y30 y31 + pmull x20 x21 y20 y21 +
              pmull x10 x11 y10 y11 + pmull x00 x01 y00 y01`;;

let pmul_acc4 = define
  `pmul_acc4 (x00: int) (x01 : int) (y00 : int) (y01 : int)
             (x10: int) (x11 : int) (y10 : int) (y11 : int)
             (x20: int) (x21 : int) (y20 : int) (y21 : int)
             (x30: int) (x31 : int) (y30 : int) (y31 : int) =
             (&(inverse_mod 3329 65536) *
    pmull_acc4 x00 x01 y00 y01 x10 x11 y10 y11 x20 x21 y20 y21
               x30 x31 y30 y31) rem &3329`;;

let basemul4_even = define
 `basemul4_even x0 y0 y0t x1 y1 y1t x2 y2 y2t x3 y3 y3t = \i.
    pmul_acc4 (x0 (2 * i)) (x0 (2 * i + 1))
              (y0 (2 * i)) (y0t i)
              (x1 (2 * i)) (x1 (2 * i + 1))
              (y1 (2 * i)) (y1t i)
              (x2 (2 * i)) (x2 (2 * i + 1))
              (y2 (2 * i)) (y2t i)
              (x3 (2 * i)) (x3 (2 * i + 1))
              (y3 (2 * i)) (y3t i)`;;

let basemul4_odd = define
 `basemul4_odd x0 y0 x1 y1 x2 y2 x3 y3 = \i.
  pmul_acc4 (x0 (2 * i)) (x0 (2 * i + 1))
            (y0 (2 * i + 1)) (y0 (2 * i))
            (x1 (2 * i)) (x1 (2 * i + 1))
            (y1 (2 * i + 1)) (y1 (2 * i))
            (x2 (2 * i)) (x2 (2 * i + 1))
            (y2 (2 * i + 1)) (y2 (2 * i))
            (x3 (2 * i)) (x3 (2 * i + 1))
            (y3 (2 * i + 1)) (y3 (2 * i))`;;

(* ------------------------------------------------------------------------- *)
(* The check for overlap. With x0 = r + 512 and x3 = b_cache + 512, cmp x3,  *)
(* x0 then ccmp x4, x3 leave the carry flag clear, taking the scalar code,   *)
(* if b_cache < r + 512 and r < b_cache + 512, computing modulo 2^64. When   *)
(* the 512 bytes from r and the m bytes from b_cache do not overlap, this    *)
(* does not happen: otherwise the start of one would be within the other,    *)
(* also when one of them wraps around the end of the address space.          *)
(* ------------------------------------------------------------------------- *)

let MOD_2N_CASES_STMT =
  `!x n. x < 2 * n ==> x MOD n = if x < n then x else x - n`;;

let MOD_2N_CASES = assume_spec MOD_2N_CASES_STMT;;

let WORD_SUB_FLAG_64_STMT =
  `!x y:int64.
     &(val x) - &(val y):int = &(val(word_sub x y)) <=> val y <= val x`;;

let WORD_SUB_FLAG_64 = assume_spec WORD_SUB_FLAG_64_STMT;;

let BASEMUL_ALIAS_STMT =
  `!dst bc:int64 m.
     nonoverlapping (dst,512) (bc,m) /\ 0 < m /\ m <= 1024
     ==> (if val bc < val (word_add dst (word 512))
          then &(val dst) - &(val (word_add bc (word m))):int =
               &(val (word_sub dst (word_add bc (word m))))
          else T)`;;

let BASEMUL_ALIAS = assume_spec BASEMUL_ALIAS_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

(*** The addresses of the coefficients relative to those of the loads and
 *** stores, in the form that the simulation gives to the addresses
 ***)

let BM_ADDR_A_STMT =
  `!a:int64 i k. word_add a (word(2 * (16 * i + k))) =
                 word_add (word_add a (word(32 * i))) (word(2 * k))`;;

let BM_ADDR_A = assume_spec BM_ADDR_A_STMT;;

let BM_ADDR_B_STMT =
  `!a:int64 i k. word_add a (word(512 + 2 * (16 * i + k))) =
                 word_add (word_add a (word(32 * i + 512))) (word(2 * k))`;;

let BM_ADDR_B = assume_spec BM_ADDR_B_STMT;;

let BM_ADDR_C_STMT =
  `!a:int64 i k. word_add a (word(2 * (8 * i + k))) =
                 word_add (word_add a (word(16 * i))) (word(2 * k))`;;

let BM_ADDR_C = assume_spec BM_ADDR_C_STMT;;

let BM_ADDR_D_STMT =
  `!a:int64 i k. word_add a (word(256 + 2 * (8 * i + k))) =
                 word_add (word_add a (word(16 * i + 256))) (word(2 * k))`;;

let BM_ADDR_D = assume_spec BM_ADDR_D_STMT;;

let BM_ADDR_B2_STMT =
  `!a:int64 i k. word_add a (word(1024 + 2 * (16 * i + k))) =
                 word_add (word_add a (word(32 * i + 1024))) (word(2 * k))`;;

let BM_ADDR_B2 = assume_spec BM_ADDR_B2_STMT;;

let BM_ADDR_D2_STMT =
  `!a:int64 i k. word_add a (word(512 + 2 * (8 * i + k))) =
                 word_add (word_add a (word(16 * i + 512))) (word(2 * k))`;;

let BM_ADDR_D2 = assume_spec BM_ADDR_D2_STMT;;

let BM_ADDR_B3_STMT =
  `!a:int64 i k. word_add a (word(1536 + 2 * (16 * i + k))) =
                 word_add (word_add a (word(32 * i + 1536))) (word(2 * k))`;;

let BM_ADDR_B3 = assume_spec BM_ADDR_B3_STMT;;

let BM_ADDR_D3_STMT =
  `!a:int64 i k. word_add a (word(768 + 2 * (8 * i + k))) =
                 word_add (word_add a (word(16 * i + 768))) (word(2 * k))`;;

let BM_ADDR_D3 = assume_spec BM_ADDR_D3_STMT;;

(*** Instantiate the quantified input fact for f at the n coefficients from
 *** m * i, with the addresses relative to the base of the vector load
 ***)

let BM_LOAD_TAC f m n ath =
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && free_in f (concl th) then
      MAP_EVERY (fun k ->
        MP_TAC(SPEC (subst [mk_small_numeral m,`m:num`;
                            mk_small_numeral k,`k:num`] `m * i + k`) th) THEN
        ANTS_TAC THENL
         [ASM_ARITH_TAC;
          DISCH_THEN(ASSUME_TAC o REWRITE_RULE[WORD_ADD_0] o
                     CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
                     REWRITE_RULE[ath])]) (0--(n-1))
    else failwith "BM_LOAD_TAC");;

let BM_ADDR_E_STMT =
  `!a:int64 i k. word_add a (word(4 * (8 * i + k))) =
                 word_add (word_add a (word(32 * i))) (word(4 * k))`;;

let BM_ADDR_E = assume_spec BM_ADDR_E_STMT;;

let BM_ADDR_F_STMT =
  `!a:int64 i k. word_add a (word(4 * (8 * i + k) + 2)) =
                 word_add (word_add a (word(32 * i))) (word(4 * k + 2))`;;

let BM_ADDR_F = assume_spec BM_ADDR_F_STMT;;

(*** The indices of the coefficients of pair 8 * i + k, for k < 8 ***)

let BM_IDX_RULES =
  List.concat (map (fun k ->
    let kt = mk_small_numeral k in
    [ARITH_RULE(subst [kt,`k:num`; mk_small_numeral(2 * k),`c:num`]
       `2 * (8 * i + k) = 16 * i + c`);
     ARITH_RULE(subst [kt,`k:num`; mk_small_numeral(2 * k + 1),`c:num`]
       `2 * (8 * i + k) + 1 = 16 * i + c`)]) (0--7));;

(*** The congruence for a lane, a Montgomery-reduced sum of products ***)

let BM4_CONG_TAC =
  ASSUM_LIST(fun ths -> W(fun (asl,w) ->
    let tm = rand(rand(lhand(rator w))) in
    let th1 = WEAKEN_INTCONG_RULE (num 3329) (GEN_CONGBOUND_RULE ths tm) in
    let th2 = MATCH_MP CONGBOUND_MONTRED_SCALAR th1 in
    let th3 = MP th2 (EQT_ELIM(INT_REDUCE_CONV(lhand(concl th2)))) in
    MP_TAC(CONJUNCT1 th3))) THEN
  REWRITE_TAC[basemul4_even; basemul4_odd;
              pmul_acc4; pmull_acc4; pmull; o_THM] THEN
  REWRITE_TAC BM_IDX_RULES THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC INT_RING;;

let basemul_k4_inputs =
 `(!i. i < 256
       ==> read(memory :> bytes16
            (word_add srcA (word (2 * i)))) s = x0 i) /\
  (!i. i < 256
       ==> read(memory :> bytes16
            (word_add srcB (word (2 * i)))) s = y0 i) /\
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
  (!i. i < 256
       ==> read(memory :> bytes16
            (word_add srcA (word (1024 + 2 * i)))) s = x2 i) /\
  (!i. i < 256
       ==> read(memory :> bytes16
            (word_add srcB (word (1024 + 2 * i)))) s = y2 i) /\
  (!i. i < 128
       ==> read(memory :> bytes16
            (word_add srcBt (word (512 + 2 * i)))) s = y2t i) /\
  (!i. i < 256
       ==> read(memory :> bytes16
            (word_add srcA (word (1536 + 2 * i)))) s = x3 i) /\
  (!i. i < 256
       ==> read(memory :> bytes16
            (word_add srcB (word (1536 + 2 * i)))) s = y3 i) /\
  (!i. i < 128
       ==> read(memory :> bytes16
            (word_add srcBt (word (768 + 2 * i)))) s = y3t i)`;;

let basemul_k4_bounds =
 `!i. i < 256
      ==> abs(ival((x0:num->int16) i)) <= &2 pow 12 /\
          abs(ival((x1:num->int16) i)) <= &2 pow 12 /\
          abs(ival((x2:num->int16) i)) <= &2 pow 12 /\
          abs(ival((x3:num->int16) i)) <= &2 pow 12`;;

let basemul_k4_outputs n =
  subst [n,`N:num`]
  `!j. j < N
       ==> (ival(read(memory :> bytes16
              (word_add dst (word (4 * j)))) s) ==
            basemul4_even
             (ival o (x0:num->int16)) (ival o (y0:num->int16))
             (ival o (y0t:num->int16)) (ival o (x1:num->int16))
             (ival o (y1:num->int16)) (ival o (y1t:num->int16))
             (ival o (x2:num->int16)) (ival o (y2:num->int16))
             (ival o (y2t:num->int16)) (ival o (x3:num->int16))
             (ival o (y3:num->int16)) (ival o (y3t:num->int16))
             j) (mod &3329) /\
           (ival(read(memory :> bytes16
              (word_add dst (word (4 * j + 2)))) s) ==
            basemul4_odd
             (ival o x0) (ival o y0) (ival o x1) (ival o y1)
             (ival o x2) (ival o y2) (ival o x3) (ival o y3)
             j) (mod &3329)`;;

(*** The loop invariant, with 8 * i pairs of outputs done ***)

let basemul_k4_inv =
  let tm =
 `\i s. aligned_bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O3_mc /\
        read X2 s = word_add srcA (word(32 * i)) /\
        read X1 s = word_add srcB (word(32 * i)) /\
        read X0 s = word_add (word_add srcBt (word(16 * i))) (word 256) /\
        read X7 s = word_add dst (word(32 * i)) /\
        read X8 s = word_add srcBt (word 512) /\
        read SP s = stackpointer /\
        read(memory :> bytes64 stackpointer) s = x19_init /\
        read(memory :> bytes64(word_add stackpointer (word 8))) s =
        x20_init /\
        read(memory :> bytes64(word_add stackpointer (word 32))) s =
        returnaddress /\
        read(memory :> bytes64(word_add stackpointer (word 48))) s =
        d8_init /\
        read(memory :> bytes64(word_add stackpointer (word 56))) s =
        d9_init /\
        read(memory :> bytes64(word_add stackpointer (word 64))) s =
        d10_init /\
        read(memory :> bytes64(word_add stackpointer (word 72))) s =
        d11_init /\
        read(memory :> bytes64(word_add stackpointer (word 80))) s =
        d12_init /\
        read(memory :> bytes64(word_add stackpointer (word 88))) s =
        d13_init /\
        read(memory :> bytes64(word_add stackpointer (word 96))) s =
        d14_init /\
        read(memory :> bytes64(word_add stackpointer (word 104))) s =
        d15_init /\
        read Q6 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
        read Q7 s = word 0xf301f301f301f301f301f301f301f301 /\
        INPUTS /\ (BOUNDS ==> OUTPUTS)` in
  let vs,bod = dest_abs tm in
  let s,body = dest_abs bod in
  mk_abs(vs,mk_abs(s,subst
   [basemul_k4_inputs,`INPUTS:bool`; basemul_k4_bounds,`BOUNDS:bool`;
    basemul_k4_outputs `8 * i`,`OUTPUTS:bool`] body));;

let basemul_k4_goal =
 `!srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t x2 y2 y2t x3 y3 y3t
   pc stackpointer returnaddress.
     aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     ALL (nonoverlapping (dst, 512))
         [(word pc, libmlkem_size); (srcA, 2048); (srcB, 2048); (srcBt, 1024);
          (word_sub stackpointer (word 128),128)] /\
     ALL (nonoverlapping (word_sub stackpointer (word 128),128))
         [(word pc, libmlkem_size); (srcA, 2048); (srcB, 2048); (srcBt, 1024)]
     ==>
     ensures arm
       (\s. aligned_bytes_loaded s (word pc)
              mlkem_native_libmlkem_gcc12_O3_mc /\
            read PC s =
              word (pc + mlkem1024_polyvec_basemul_acc_montgomery_cached) /\
            read SP s = stackpointer /\
            read X30 s = returnaddress /\
            C_ARGUMENTS [dst; srcA; srcB; srcBt] s  /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (2 * i)))) s = x0 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB (word (2 * i)))) s = y0 i) /\
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
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (1024 + 2 * i)))) s = x2 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB (word (1024 + 2 * i)))) s = y2 i) /\
            (!i. i < 128
                 ==> read(memory :> bytes16
                      (word_add srcBt (word (512 + 2 * i)))) s = y2t i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (1536 + 2 * i)))) s = x3 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB (word (1536 + 2 * i)))) s = y3 i) /\
            (!i. i < 128
                 ==> read(memory :> bytes16
                      (word_add srcBt (word (768 + 2 * i)))) s = y3t i))
       (\s. read PC s = returnaddress /\
            ((!i. i < 256
                  ==> abs(ival(x0 i)) <= &2 pow 12 /\
                       abs(ival(x1 i)) <= &2 pow 12 /\
                       abs(ival(x2 i)) <= &2 pow 12 /\
                       abs(ival(x3 i)) <= &2 pow 12)
             ==> (!i. i < 128
                      ==> (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i)))) s) ==
                           basemul4_even
                            (ival o x0) (ival o y0) (ival o y0t) (ival o x1)
                            (ival o y1) (ival o y1t) (ival o x2) (ival o y2)
                            (ival o y2t) (ival o x3) (ival o y3) (ival o y3t)
                            i) (mod &3329) /\
                          (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i + 2)))) s) ==
                           basemul4_odd
                            (ival o x0) (ival o y0) (ival o x1) (ival o y1)
                            (ival o x2) (ival o y2) (ival o x3) (ival o y3)
                            i) (mod &3329))))
       (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
        MAYCHANGE [memory :> bytes(dst, 512);
                   memory :> bytes(word_sub stackpointer (word 128),128)])`;;

(*** The vector of 3329^-1 mod 2^16 in the image ***)

let MLKEM_NATIVE_BASEMUL_K4_GCC12_O3_CONSTANTS =
  MLKEM_NATIVE_IMAGE_CONST_RULE
   (layout "mlkem1024_polyvec_basemul_acc_montgomery_cached_consts") 128;;

let MLKEM_NATIVE_BASEMUL_K4_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  basemul_k4_goal;;

let MLKEM_NATIVE_BASEMUL_K4_GCC12_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_BASEMUL_K4_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let WORD_ZX_ZX_64_128_STMT =
  `!x:int64. word_zx(word_zx x:int128):int64 = x`;;

let WORD_ZX_ZX_64_128 = assume_spec WORD_ZX_ZX_64_128_STMT;;

(*** The C signature is the same as that of mlkem_basemul_k4, and the code
 *** also reads the vector of 3329^-1 mod 2^16
 ***)

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:
      [`word(pc + mlkem1024_polyvec_basemul_acc_montgomery_cached_consts)
        :int64`,
       `mlkem1024_polyvec_basemul_acc_montgomery_cached_consts_size:num`]
    ~keep_maychanges:true
    (assoc "mlkem_basemul_k4" subroutine_signatures)
    MLKEM_NATIVE_BASEMUL_K4_GCC12_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_BASEMUL_K4_GCC12_O3_EXEC;;

let MLKEM_NATIVE_BASEMUL_K4_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e srcA srcB srcBt dst pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       ALL (nonoverlapping (dst,512))
           [word pc,libmlkem_size; srcA,2048; srcB,2048; srcBt,1024;
            word_sub stackpointer (word 128),128] /\
       ALL (nonoverlapping (word_sub stackpointer (word 128),128))
           [word pc,libmlkem_size; srcA,2048; srcB,2048; srcBt,1024]
       ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  mlkem_native_libmlkem_gcc12_O3_mc /\
                read PC s =
                  word (pc +
                        mlkem1024_polyvec_basemul_acc_montgomery_cached) /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [dst; srcA; srcB; srcBt] s /\
                read events s = e)
           (\s. read PC s = returnaddress /\
                exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_events srcA srcB srcBt dst pc
                         (word_sub stackpointer (word 128)) returnaddress /\
                  memaccess_inbounds e2
                   [srcA,2048; srcB,2048; srcBt,1024; dst,512;
                    word_sub stackpointer (word 128),128;
                    word (pc +
                      mlkem1024_polyvec_basemul_acc_montgomery_cached_consts),
                    mlkem1024_polyvec_basemul_acc_montgomery_cached_consts_size
                   ]
                   [dst,512; word_sub stackpointer (word 128),128])
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
            MAYCHANGE
             [memory :> bytes(dst, 512);
              memory :> bytes(word_sub stackpointer (word 128),128)])`;;

let MLKEM_NATIVE_BASEMUL_K4_GCC12_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_BASEMUL_K4_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
