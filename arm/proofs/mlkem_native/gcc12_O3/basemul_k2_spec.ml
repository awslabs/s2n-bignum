(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Scalar product of 2-element polynomial vectors in NTT domain.             *)
(* This is the code for mlkem512_polyvec_basemul_acc_montgomery_cached from  *)
(* mlkem-native's portable C implementation compiled by gcc 12 with -O3      *)
(* (see mlkem_native/README.md), verified in the whole image (see            *)
(* libmlkem.ml) with the specification of the -O2 code.                      *)
(*                                                                           *)
(* At -O2 the code is a scalar loop over the 128 pairs of coefficients. At   *)
(* -O3 gcc has vectorized it: unless the output may overlap the cache of     *)
(* products of the second input, by a check that computes with the           *)
(* addresses modulo 2^64, a loop computes 8 pairs at a time, loading 16      *)
(* coefficients of each input with LD2, which splits them into the even and  *)
(* odd ones, and storing them with ST2. Otherwise it uses a scalar loop      *)
(* like that of -O2. When the output and the cache do not overlap the check  *)
(* always takes the vector loop, so that is the only path verified here.     *)
(*                                                                           *)
(* The vector loop loads the vector of 3329^-1 mod 2^16 from the read-only   *)
(* data, so the safety theorem lists that vector, of                         *)
(* mlkem512_polyvec_basemul_acc_montgomery_cached_consts_size bytes, as a    *)
(* read-only region, which the -O2 theorem does not have.                    *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;

let MLKEM_NATIVE_BASEMUL_K2_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem512_polyvec_basemul_acc_montgomery_cached"];;

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

let BM_CONG_TAC =
  ASSUM_LIST(fun ths -> W(fun (asl,w) ->
    let tm = rand(rand(lhand(rator w))) in
    let th1 = WEAKEN_INTCONG_RULE (num 3329) (GEN_CONGBOUND_RULE ths tm) in
    let th2 = MATCH_MP CONGBOUND_MONTRED_SCALAR th1 in
    let th3 = MP th2 (EQT_ELIM(INT_REDUCE_CONV(lhand(concl th2)))) in
    MP_TAC(CONJUNCT1 th3))) THEN
  REWRITE_TAC[basemul2_even; basemul2_odd;
              pmul_acc2; pmull_acc2; pmull; o_THM] THEN
  REWRITE_TAC BM_IDX_RULES THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC INT_RING;;

(*** The loop invariant, with 8 * i pairs of outputs done ***)

let basemul_k2_inv =
 `\i s. aligned_bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O3_mc /\
        read X0 s = word_add srcA (word(32 * i)) /\
        read X1 s = word_add srcB (word(32 * i)) /\
        read X2 s = word_add srcBt (word(16 * i)) /\
        read X4 s = word_add dst (word(32 * i)) /\
        read X6 s = word_add srcB (word 512) /\
        read X30 s = returnaddress /\
        read Q18 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
        read Q19 s = word 0xf301f301f301f301f301f301f301f301 /\
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
         ==> (!j. j < 8 * i
                  ==> (ival(read(memory :> bytes16
                         (word_add dst (word (4 * j)))) s) ==
                       basemul2_even (ival o x0) (ival o y0) (ival o y0t)
                                     (ival o x1) (ival o y1) (ival o y1t)
                                     j) (mod &3329) /\
                      (ival(read(memory :> bytes16
                         (word_add dst (word (4 * j + 2)))) s) ==
                       basemul2_odd (ival o x0) (ival o y0) (ival o x1)
                       (ival o y1) j) (mod &3329)))`;;

let basemul_k2_goal =
 `!srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t pc returnaddress.
     aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
     ALL (nonoverlapping (dst, 512))
         [(word pc, libmlkem_size); (srcA, 1024); (srcB, 1024); (srcBt, 512)]
     ==>
     ensures arm
       (\s. aligned_bytes_loaded s (word pc)
              mlkem_native_libmlkem_gcc12_O3_mc /\
            read PC s =
              word (pc + mlkem512_polyvec_basemul_acc_montgomery_cached) /\
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
       (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
        MAYCHANGE [memory :> bytes(dst, 512)])`;;

(*** The vector of 3329^-1 mod 2^16 in the image ***)

let MLKEM_NATIVE_BASEMUL_K2_GCC12_O3_CONSTANTS =
  MLKEM_NATIVE_IMAGE_CONST_RULE
   (layout "mlkem512_polyvec_basemul_acc_montgomery_cached_consts") 128;;

let MLKEM_NATIVE_BASEMUL_K2_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  basemul_k2_goal;;

let MLKEM_NATIVE_BASEMUL_K2_GCC12_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_BASEMUL_K2_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The C signature is the same as that of mlkem_basemul_k2, and the code
 *** also reads the vector of 3329^-1 mod 2^16
 ***)

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:
      [`word(pc + mlkem512_polyvec_basemul_acc_montgomery_cached_consts)
        :int64`,
       `mlkem512_polyvec_basemul_acc_montgomery_cached_consts_size:num`]
    ~keep_maychanges:true
    (assoc "mlkem_basemul_k2" subroutine_signatures)
    MLKEM_NATIVE_BASEMUL_K2_GCC12_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_BASEMUL_K2_GCC12_O3_EXEC;;

let MLKEM_NATIVE_BASEMUL_K2_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e srcA srcB srcBt dst pc returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       ALL (nonoverlapping (dst,512))
           [word pc,libmlkem_size; srcA,1024; srcB,1024; srcBt,512]
       ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  mlkem_native_libmlkem_gcc12_O3_mc /\
                read PC s =
                  word (pc + mlkem512_polyvec_basemul_acc_montgomery_cached) /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [dst; srcA; srcB; srcBt] s /\
                read events s = e)
           (\s. read PC s = returnaddress /\
                exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_events srcA srcB srcBt dst pc returnaddress /\
                  memaccess_inbounds e2
                   [srcA,1024; srcB,1024; srcBt,512; dst,512;
                    word (pc +
                      mlkem512_polyvec_basemul_acc_montgomery_cached_consts),
                    mlkem512_polyvec_basemul_acc_montgomery_cached_consts_size]
                   [dst,512])
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
            MAYCHANGE [memory :> bytes(dst, 512)])`;;

let MLKEM_NATIVE_BASEMUL_K2_GCC12_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_BASEMUL_K2_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
