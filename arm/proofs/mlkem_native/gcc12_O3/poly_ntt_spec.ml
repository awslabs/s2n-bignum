(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Forward number-theoretic transform from ML-KEM.                           *)
(* This is the code for mlkem_poly_ntt from mlkem-native's portable C        *)
(* implementation compiled by gcc 12 with -O3 (see mlkem_native/README.md),  *)
(* verified in the whole image (see libmlkem.ml) with the specification of   *)
(* the -O2 code.                                                             *)
(*                                                                           *)
(* The layers and blocks are loops as at -O2, but gcc has vectorized the     *)
(* butterflies of a block. Unless the two halves of the block may overlap in *)
(* 16 bytes, by a check that computes with the addresses modulo 2^64, it     *)
(* does them 8 at a time with 128-bit vectors and then any rest 4 at a time  *)
(* with 64-bit vectors and one by one. Otherwise it does them one by one as  *)
(* at -O2. Here the halves have 2^(7-l) coefficients in layer l + 1, so the  *)
(* first five layers take the loop over 128-bit vectors, the last one the    *)
(* scalar loop, and the sixth, with 4 + 4 coefficients, the scalar loop      *)
(* unless the 24 bytes from the start of the block wrap around the end of    *)
(* the address space, in which case it takes the code for 64-bit vectors.    *)
(*                                                                           *)
(* Unlike the -O2 code, it saves X19, X20, X21 and X30 on the stack, so its  *)
(* specification has a stack frame of 32 bytes, and it loads the vector of   *)
(* 3329^-1 mod 2^16 from mlkem_poly_ntt_consts, so the safety theorem lists  *)
(* that block as read-only data besides the zetas.                           *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;
needs "common/int_linear.ml";;

let MLKEM_NATIVE_POLY_NTT_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem_poly_ntt"];;

(* ------------------------------------------------------------------------- *)
(* The computation done by the C code, with its 16-bit and 32-bit integer    *)
(* arithmetic, as for gcc 12 -O2. The NTT is done in 7 layers, layer l+1     *)
(* consisting of 2^l blocks of 2^(8-l) consecutive coefficients. A block     *)
(* uses one zeta to do butterflies on pairs of coefficients 2^(7-l) apart,   *)
(* independently.                                                            *)
(* ------------------------------------------------------------------------- *)

let ntt_fqmul_c = define
 `ntt_fqmul_c (z:int16) (y:int16) =
    montred_scalar(word_mul (word_sx y) (word_sx z))`;;

let ntt_block_c = define
 `ntt_block_c (z:int16) start len (m:num->int16) i =
    if start <= i /\ i < start + len
    then word_add (m i) (ntt_fqmul_c z (m(i + len)))
    else if start + len <= i /\ i < start + 2 * len
    then word_sub (m(i - len)) (ntt_fqmul_c z (m i))
    else m i`;;

let ntt_blocks_c = define
 `ntt_blocks_c l 0 (r:num->int16) = r /\
  ntt_blocks_c l (SUC b) r =
    ntt_block_c (iword(EL (2 EXP l + b) mlk_zetas))
                (2 * 2 EXP (7 - l) * b) (2 EXP (7 - l))
                (ntt_blocks_c l b r)`;;

let ntt_layers_c = define
 `ntt_layers_c 0 (x:num->int16) = x /\
  ntt_layers_c (SUC l) x = ntt_blocks_c l (2 EXP l) (ntt_layers_c l x)`;;

(* ------------------------------------------------------------------------- *)
(* Lemmas about the code.                                                    *)
(* ------------------------------------------------------------------------- *)

(*** Splitting off the 8 coefficients of one iteration of the vector loop,
 *** and their addresses relative to those of the two 128-bit loads
 ***)

let RANGE8_SPLIT_STMT =
  `!P i n. 8 * (i + 1) <= n
           ==> ((!j. 8 * i <= j /\ j < n ==> P j) <=>
                (!j. 8 * (i + 1) <= j /\ j < n ==> P j) /\
                (!k. k < 8 ==> P(8 * i + k)))`;;

let RANGE8_SPLIT = assume_spec RANGE8_SPLIT_STMT;;

let NTT_VEC_ADDR_STMT =
  `!a n i k. word_add a (word(2 * (n + (8 * i + k)))):int64 =
             word_add (word_add a (word(2 * n + 16 * i))) (word(2 * k))`;;

let NTT_VEC_ADDR = assume_spec NTT_VEC_ADDR_STMT;;

let NTT_VEC_ADDR2_STMT =
  `!a n l i k. word_add a (word(2 * (n + l + (8 * i + k)))):int64 =
               word_add (word_add a (word(2 * (n + l) + 16 * i)))
                        (word(2 * k))`;;

let NTT_VEC_ADDR2 = assume_spec NTT_VEC_ADDR2_STMT;;

(*** The butterflies of a block, for the lower and the upper half ***)

let NTT_BLOCK_C_LO8_STMT =
  `!z start len m i k.
     8 * (i + 1) <= len /\ k < 8
     ==> ntt_block_c z start len m (start + 8 * i + k) =
         word_add (m(start + 8 * i + k))
                  (ntt_fqmul_c z (m(start + len + 8 * i + k)))`;;

let NTT_BLOCK_C_LO8 = assume_spec NTT_BLOCK_C_LO8_STMT;;

let NTT_BLOCK_C_HI8_STMT =
  `!z start len m i k.
     8 * (i + 1) <= len /\ k < 8
     ==> ntt_block_c z start len m (start + len + 8 * i + k) =
         word_sub (m(start + 8 * i + k))
                  (ntt_fqmul_c z (m(start + len + 8 * i + k)))`;;

let NTT_BLOCK_C_HI8 = assume_spec NTT_BLOCK_C_HI8_STMT;;

(*** The coefficients of a block, from its parts below, inside and above ***)

let NTT_BLOCK_JOIN_STMT =
  `!(P:num->int16) z start len m.
     start + 2 * len <= 256 /\
     (!j. j < start ==> P j = m j) /\
     (!j. start + 2 * len <= j /\ j < 256 ==> P j = m j) /\
     (!j. j < len ==> P(start + j) = ntt_block_c z start len m (start + j)) /\
     (!j. j < len
          ==> P(start + len + j) = ntt_block_c z start len m (start + len + j))
     ==> !i. i < 256 ==> P i = ntt_block_c z start len m i`;;

let NTT_BLOCK_JOIN = assume_spec NTT_BLOCK_JOIN_STMT;;

(*** The zeta duplicated in the lanes of a vector, from W6 ***)

let WORD_ZX_ZX_SX_16_STMT =
  `!z:int16. word_zx(word_zx(word_sx z:int32):int64):int16 = z`;;

let WORD_ZX_ZX_SX_16 = assume_spec WORD_ZX_ZX_SX_16_STMT;;

(*** The test of the low 3 bits of the length after the vector loop ***)

let WORD_AND_8N_7_STMT =
  `!n. word_and (word(8 * n):int64) (word 7) = word 0`;;

let WORD_AND_8N_7 = assume_spec WORD_AND_8N_7_STMT;;

(*** The values of registers computed from small numbers. REG_SMALL_TAC r v
 *** replaces the value of register r in the assumptions by v, proving the
 *** equation as WORD_SMALL_TAC does, but also with shifts right
 ***)

let NTT_DIV8_STMT =
  `!n. (8 * n) DIV 8 = n`;;

let NTT_DIV8 = assume_spec NTT_DIV8_STMT;;

let NTT_SMALL_TAC =
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; WORD_ADD_LCANCEL_EQ] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_SUB_CASES; VAL_WORD_ZX_GEN;
              VAL_WORD; VAL_WORD_SHL; VAL_WORD_USHR;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(MOD_LT_ASM_TAC ORELSE CHANGED_TAC(REWRITE_TAC[NTT_DIV8]) ORELSE
         (COND_CASES_TAC THEN TRY(FIRST_ASSUM(fun th ->
            if is_neg(concl th) then
              (MP_TAC th THEN SIMPLE_ARITH_TAC) else NO_TAC)))) THEN
  SIMPLE_ARITH_TAC;;

let REG_SMALL_TAC r v =
  FIRST_X_ASSUM(fun th ->
    let l,t = dest_eq(concl th) in
    if is_comb l && is_comb(rator l) && rand(rator l) = r
    then SUBGOAL_THEN (mk_eq(t,v)) (fun eth -> ASSUME_TAC(TRANS th eth)) THENL
          [NTT_SMALL_TAC; ALL_TAC]
    else failwith "REG_SMALL_TAC");;

let REG_REWRITE_TAC r ths =
  FIRST_X_ASSUM(fun th ->
    let l,t = dest_eq(concl th) in
    if is_comb l && is_comb(rator l) && rand(rator l) = r
    then ASSUME_TAC(REWRITE_RULE ths th)
    else failwith "REG_REWRITE_TAC");;

(*** The checks before the vector loop: cmp x3, x21 then ccmp x2, x0 set
 *** the carry flag, taking the vector code, unless the lower half of the
 *** block, from x2, and the upper half, from x3, may overlap in 16 bytes,
 *** computing with the addresses modulo 2^64. For a block of 8 * n + 8 * n
 *** coefficients the vector code is taken even if the addresses wrap
 *** around, and for one of 4 + 4 it is not taken unless they do.
 ***)

let MOD_2N_CASES_STMT =
  `!x n. x < 2 * n ==> x MOD n = if x < n then x else x - n`;;

let MOD_2N_CASES = assume_spec MOD_2N_CASES_STMT;;

let VAL_WORD_ADD_SMALL_CASES_STMT =
  `!a:int64 p. p < 2 EXP 64
     ==> val(word_add a (word p)) =
         if val a + p < 2 EXP 64 then val a + p else (val a + p) - 2 EXP 64`;;

let VAL_WORD_ADD_SMALL_CASES = assume_spec VAL_WORD_ADD_SMALL_CASES_STMT;;

let WORD_SUB_FLAG_64_STMT =
  `!x y:int64.
     &(val x) - &(val y):int = &(val(word_sub x y)) <=> val y <= val x`;;

let WORD_SUB_FLAG_64 = assume_spec WORD_SUB_FLAG_64_STMT;;

let VAL_WORD_ADD_CASES_TAC =
  REPEAT(W(fun (asl,w) ->
    let t = find_term
      (can (term_match [] `val(word_add (a:int64) (word p))`)) w in
    MP_TAC(PART_MATCH (lhand o rand) VAL_WORD_ADD_SMALL_CASES t) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC]));;

let NTT_ALIAS_VEC_STMT =
  `!a:int64 p q.
     q + 16 <= p /\ p + 16 < 2 EXP 64
     ==> (if val(word_add a (word p)) < val(word_add a (word(q + 16)))
          then &(val(word_add a (word q))) -
               &(val(word_add a (word(p + 16)))):int =
               &(val(word_sub (word_add a (word q))
                              (word_add a (word(p + 16)))))
          else T)`;;

let NTT_ALIAS_VEC = assume_spec NTT_ALIAS_VEC_STMT;;

let NTT_ALIAS_SCALAR_STMT =
  `!a:int64 q.
     val(word_add a (word q)) + 24 < 2 EXP 64 /\ q + 24 < 2 EXP 64
     ==> ((if val(word_add a (word(q + 8))) < val(word_add a (word(q + 16)))
           then &(val(word_add a (word q))) -
                &(val(word_add a (word(q + 24)))):int =
                &(val(word_sub (word_add a (word q))
                               (word_add a (word(q + 24)))))
           else T) <=> F)`;;

let NTT_ALIAS_SCALAR = assume_spec NTT_ALIAS_SCALAR_STMT;;

(* ------------------------------------------------------------------------- *)
(* One block of the first five layers, with n vectors of 8 coefficients in   *)
(* each half, from the head of the block loop through the vector loop.       *)
(* ------------------------------------------------------------------------- *)

let ntt_vblock_inv =
 `\i s. aligned_bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O3_mc /\
        read X0 s = word(16 * i) /\
        read X2 s = word_add a (word(2 * start)) /\
        read X3 s = word_add a (word(2 * (start + 8 * n))) /\
        read X19 s = word(16 * n) /\ read X20 s = word(8 * n) /\
        read Q4 s = word_duplicate z /\
        read X4 s = a /\ read X17 s = word_add a (word 2) /\
        read X7 s = word start /\ read X10 s = word(start + 8 * n) /\
        read X11 s = word(k + 1) /\
        read X6 s = word_zx(word_sx z:int32) /\
        read X12 s = word(16 * n) /\ read X13 s = word(8 * n) /\
        read X15 s = word(8 * n) /\
        read X8 s = word 4294963967 /\ read X9 s = word 4294963969 /\
        read X14 s = word zetas /\ read X16 s = w16 /\
        read X18 s = word 1 /\ read X30 s = word 256 /\
        read Q5 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
        read Q6 s = word 0xf301f301f301f301f301f301f301f301 /\
        read Q7 s = word 0xf301f301f301f301 /\
        read Q16 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
        (!k. k < 128
             ==> read(memory :> bytes16(word_add (word zetas)
                                                 (word(2 * k)))) s =
                 iword(EL k mlk_zetas)) /\
        (!j. j < start
             ==> read(memory :> bytes16(word_add a (word(2 * j)))) s = m j) /\
        (!j. start + 16 * n <= j /\ j < 256
             ==> read(memory :> bytes16(word_add a (word(2 * j)))) s = m j) /\
        (!j. j < 8 * i
             ==> read(memory :> bytes16(word_add a (word(2 * (start + j)))))
                   s =
                 ntt_block_c z start (8 * n) m (start + j)) /\
        (!j. 8 * i <= j /\ j < 8 * n
             ==> read(memory :> bytes16(word_add a (word(2 * (start + j)))))
                   s =
                 m (start + j)) /\
        (!j. j < 8 * i
             ==> read(memory :> bytes16(word_add a
                         (word(2 * (start + 8 * n + j))))) s =
                 ntt_block_c z start (8 * n) m (start + 8 * n + j)) /\
        (!j. 8 * i <= j /\ j < 8 * n
             ==> read(memory :> bytes16(word_add a
                         (word(2 * (start + 8 * n + j))))) s =
                 m (start + 8 * n + j))`;;

let MLKEM_NATIVE_POLY_NTT_GCC12_O3_VBLOCK_STMT =
  `!a zetas pc (z:int16) start n k (m:num->int16) w16.
     ALL (nonoverlapping (a,512))
         [(word pc,libmlkem_size); (word zetas,256)] /\
     1 <= n /\ start + 16 * n <= 256 /\ k < 256
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O3_mc /\
               read PC s = word(pc + mlkem_poly_ntt_loop2) /\
               read X4 s = a /\ read X17 s = word_add a (word 2) /\
               read X7 s = word start /\ read X10 s = word(start + 8 * n) /\
               read X11 s = word k /\
               read X6 s = word_zx(word_sx z:int32) /\
               read X12 s = word(16 * n) /\ read X13 s = word(8 * n) /\
               read X15 s = word(8 * n) /\
               read X8 s = word 4294963967 /\ read X9 s = word 4294963969 /\
               read X14 s = word zetas /\ read X16 s = w16 /\
               read X18 s = word 1 /\ read X30 s = word 256 /\
               read Q5 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
               read Q6 s = word 0xf301f301f301f301f301f301f301f301 /\
               read Q7 s = word 0xf301f301f301f301 /\
               read Q16 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        m i))
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O3_mc /\
               read PC s = word(pc + mlkem_poly_ntt_loop2_test1) /\
               read X4 s = a /\ read X17 s = word_add a (word 2) /\
               read X7 s = word(start + 16 * n) /\
               read X10 s = word(start + 24 * n) /\
               read X11 s = word(k + 1) /\
               read X6 s = word_zx(word_sx z:int32) /\
               read X12 s = word(16 * n) /\ read X13 s = word(8 * n) /\
               read X15 s = word(8 * n) /\
               read X8 s = word 4294963967 /\ read X9 s = word 4294963969 /\
               read X14 s = word zetas /\ read X16 s = w16 /\
               read X18 s = word 1 /\ read X30 s = word 256 /\
               read Q5 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
               read Q6 s = word 0xf301f301f301f301f301f301f301f301 /\
               read Q7 s = word 0xf301f301f301f301 /\
               read Q16 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        ntt_block_c z start (8 * n) m i))
          (MAYCHANGE [PC; X0; X1; X2; X3; X5; X7; X10; X11; X19; X20; X21] ,,
           MAYCHANGE [Q0; Q1; Q2; Q3; Q4] ,, MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_NTT_GCC12_O3_VBLOCK =
  assume_spec MLKEM_NATIVE_POLY_NTT_GCC12_O3_VBLOCK_STMT;;

(* ------------------------------------------------------------------------- *)
(* One block of the last two layers, with 2 or 4 coefficients in each half,  *)
(* from the head of the block loop through the scalar loop. For 4 + 4        *)
(* coefficients, this is the path of the code when the 24 bytes from the     *)
(* start of the block do not wrap around the end of the address space.       *)
(* ------------------------------------------------------------------------- *)

let ntt_sblock_inv =
 `\jj s. aligned_bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O3_mc /\
         read X1 s = word_add a (word(2 * (start + jj))) /\
         read X19 s = word_add a (word(2 * (start + len))) /\
         read X5 s = word len /\
         read X4 s = a /\ read X17 s = word_add a (word 2) /\
         read X7 s = word start /\ read X10 s = word(start + len) /\
         read X11 s = word(k + 1) /\
         read X6 s = word_zx(word_sx z:int32) /\
         read X12 s = word(2 * len) /\ read X13 s = word len /\
         read X15 s = word len /\
         read X8 s = word 4294963967 /\ read X9 s = word 4294963969 /\
         read X14 s = word zetas /\ read X16 s = w16 /\
         read X18 s = word 1 /\ read X30 s = word 256 /\
         read Q5 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
         read Q6 s = word 0xf301f301f301f301f301f301f301f301 /\
         read Q7 s = word 0xf301f301f301f301 /\
         read Q16 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
         (!k. k < 128
              ==> read(memory :> bytes16(word_add (word zetas)
                                                  (word(2 * k)))) s =
                  iword(EL k mlk_zetas)) /\
         (!i. i < 256
              ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                  if start <= i /\ i < start + jj \/
                     start + len <= i /\ i < start + len + jj
                  then ntt_block_c z start len m i else m i)`;;

(*** The setup of the scalar loop at join1 ***)

let NTT_SBLOCK_JOIN1_TAC =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O3_EXEC (1--5) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `~(a <= i /\ i < a:num)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN NTT_SMALL_TAC;;

let MLKEM_NATIVE_POLY_NTT_GCC12_O3_SBLOCK_STMT =
  `!a zetas pc (z:int16) start len k (m:num->int16) w16.
     ALL (nonoverlapping (a,512))
         [(word pc,libmlkem_size); (word zetas,256)] /\
     (len = 2 \/
      len = 4 /\ val(word_add a (word(2 * start))) + 24 < 2 EXP 64) /\
     start + 2 * len <= 256 /\ k < 256
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O3_mc /\
               read PC s = word(pc + mlkem_poly_ntt_loop2) /\
               read X4 s = a /\ read X17 s = word_add a (word 2) /\
               read X7 s = word start /\ read X10 s = word(start + len) /\
               read X11 s = word k /\
               read X6 s = word_zx(word_sx z:int32) /\
               read X12 s = word(2 * len) /\ read X13 s = word len /\
               read X15 s = word len /\
               read X8 s = word 4294963967 /\ read X9 s = word 4294963969 /\
               read X14 s = word zetas /\ read X16 s = w16 /\
               read X18 s = word 1 /\ read X30 s = word 256 /\
               read Q5 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
               read Q6 s = word 0xf301f301f301f301f301f301f301f301 /\
               read Q7 s = word 0xf301f301f301f301 /\
               read Q16 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        m i))
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O3_mc /\
               read PC s = word(pc + mlkem_poly_ntt_loop2_test1) /\
               read X4 s = a /\ read X17 s = word_add a (word 2) /\
               read X7 s = word(start + 2 * len) /\
               read X10 s = word(start + 3 * len) /\
               read X11 s = word(k + 1) /\
               read X6 s = word_zx(word_sx z:int32) /\
               read X12 s = word(2 * len) /\ read X13 s = word len /\
               read X15 s = word len /\
               read X8 s = word 4294963967 /\ read X9 s = word 4294963969 /\
               read X14 s = word zetas /\ read X16 s = w16 /\
               read X18 s = word 1 /\ read X30 s = word 256 /\
               read Q5 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
               read Q6 s = word 0xf301f301f301f301f301f301f301f301 /\
               read Q7 s = word 0xf301f301f301f301 /\
               read Q16 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        ntt_block_c z start len m i))
          (MAYCHANGE [PC; X0; X1; X2; X3; X5; X7; X10; X11; X19; X20; X21] ,,
           MAYCHANGE [Q0; Q1; Q2; Q3; Q4] ,, MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_NTT_GCC12_O3_SBLOCK =
  assume_spec MLKEM_NATIVE_POLY_NTT_GCC12_O3_SBLOCK_STMT;;

(* ------------------------------------------------------------------------- *)
(* One block of 4 + 4 coefficients when the 24 bytes from its start wrap     *)
(* around the end of the address space. The check before the vector loop    *)
(* then takes the vector code, which goes on to the code for 4 coefficients  *)
(* in each half with 64-bit vectors, from join4.                             *)
(* ------------------------------------------------------------------------- *)

let NTT_ALIAS_SCALAR_WRAP_STMT =
  `!a:int64 q.
     ~(val(word_add a (word q)) + 24 < 2 EXP 64) /\ q + 24 < 2 EXP 64
     ==> (if val(word_add a (word(q + 8))) < val(word_add a (word(q + 16)))
          then &(val(word_add a (word q))) -
               &(val(word_add a (word(q + 24)))):int =
               &(val(word_sub (word_add a (word q))
                              (word_add a (word(q + 24)))))
          else T)`;;

let NTT_ALIAS_SCALAR_WRAP = assume_spec NTT_ALIAS_SCALAR_WRAP_STMT;;

(*** The lanes of the code for 64-bit vectors, a Montgomery multiplication
 *** with the 32-bit products and quotients sign-extended
 ***)

let WORD_ZX_ZX_SX_32_STMT =
  `!z:int16. word_zx(word_zx(word_sx z:int32):int64):int32 = word_sx z`;;

let WORD_ZX_ZX_SX_32 = assume_spec WORD_ZX_ZX_SX_32_STMT;;

let WORD_USHR16_SUBWORD_STMT =
  `!x t:int32. word_subword (word_ushr (word_add x t) 16) (0,16):int16 =
               word_subword (word_add t x) (16,16)`;;

let WORD_USHR16_SUBWORD = assume_spec WORD_USHR16_SUBWORD_STMT;;

let WORD_SUBWORD_ZX_64_STMT =
  `(!x:int64. word_subword (word_subword x (0,128):int128) (0,16):int16 =
              word_subword x (0,16)) /\
   (!x:int64. word_subword (word_subword x (0,128):int128) (16,16):int16 =
              word_subword x (16,16)) /\
   (!x:int64. word_subword (word_subword x (0,128):int128) (32,16):int16 =
              word_subword x (32,16)) /\
   (!x:int64. word_subword (word_subword x (0,128):int128) (48,16):int16 =
              word_subword x (48,16)) /\
   (!x:int64. word_zx (word_zx x:int128):int64 = x)`;;

let WORD_SUBWORD_ZX_64 = assume_spec WORD_SUBWORD_ZX_64_STMT;;

let NTT_D_ADDR_STMT =
  `!a n k. word_add a (word(2 * (n + k))):int64 =
           word_add (word_add a (word(2 * n))) (word(2 * k))`;;

let NTT_D_ADDR = assume_spec NTT_D_ADDR_STMT;;

let NTT_D_ADDR2_STMT =
  `!a n k. word_add a (word(2 * (n + 4 + k))):int64 =
           word_add (word_add a (word(2 * (n + 4)))) (word(2 * k))`;;

let NTT_D_ADDR2 = assume_spec NTT_D_ADDR2_STMT;;

let NTT_BLOCK_C_LO_STMT =
  `!z start len m j.
     j < len
     ==> ntt_block_c z start len m (start + j) =
         word_add (m(start + j)) (ntt_fqmul_c z (m(start + len + j)))`;;

let NTT_BLOCK_C_LO = assume_spec NTT_BLOCK_C_LO_STMT;;

let NTT_BLOCK_C_HI_STMT =
  `!z start len m j.
     j < len
     ==> ntt_block_c z start len m (start + len + j) =
         word_sub (m(start + j)) (ntt_fqmul_c z (m(start + len + j)))`;;

let NTT_BLOCK_C_HI = assume_spec NTT_BLOCK_C_HI_STMT;;

(*** Split the coefficients of the block into those below, inside and above,
 *** with those inside as bytes16 at addresses from the two 64-bit loads
 ***)

let NTT_DBLOCK_SPLIT_TAC =
  SUBGOAL_THEN
   `(!j. j < start
         ==> read(memory :> bytes16(word_add a (word(2 * j)))) s0 = m j) /\
    (!j. start + 8 <= j /\ j < 256
         ==> read(memory :> bytes16(word_add a (word(2 * j)))) s0 = m j)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && free_in `m:num->int16` (concl th) &&
       can (term_match [] `!i. i < 256 ==> P i`) (concl th) then
      let rule ath =
        REWRITE_RULE[WORD_ADD_0] o
        CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o REWRITE_RULE[ath] in
      let ths = map (fun k -> SPEC (subst [mk_small_numeral k,`K:num`]
                                          `start + K`) th,
                              rule NTT_D_ADDR) (0--3) @
                map (fun k -> SPEC (subst [mk_small_numeral k,`K:num`]
                                          `start + 4 + K`) th,
                              rule NTT_D_ADDR2) (0--3) in
      MAP_EVERY (fun (t,r) -> MP_TAC t THEN ANTS_TAC THENL
                  [ASM_ARITH_TAC; DISCH_THEN(ASSUME_TAC o r)]) ths
    else failwith "NTT_DBLOCK_SPLIT_TAC");;

let ntt_block_goal hyp =
  let tm =
  `!a zetas pc (z:int16) start len k (m:num->int16) w16.
     ALL (nonoverlapping (a,512))
         [(word pc,libmlkem_size); (word zetas,256)] /\
     HYP /\ start + 2 * len <= 256 /\ k < 256
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O3_mc /\
               read PC s = word(pc + mlkem_poly_ntt_loop2) /\
               read X4 s = a /\ read X17 s = word_add a (word 2) /\
               read X7 s = word start /\ read X10 s = word(start + len) /\
               read X11 s = word k /\
               read X6 s = word_zx(word_sx z:int32) /\
               read X12 s = word(2 * len) /\ read X13 s = word len /\
               read X15 s = word len /\
               read X8 s = word 4294963967 /\ read X9 s = word 4294963969 /\
               read X14 s = word zetas /\ read X16 s = w16 /\
               read X18 s = word 1 /\ read X30 s = word 256 /\
               read Q5 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
               read Q6 s = word 0xf301f301f301f301f301f301f301f301 /\
               read Q7 s = word 0xf301f301f301f301 /\
               read Q16 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        m i))
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O3_mc /\
               read PC s = word(pc + mlkem_poly_ntt_loop2_test1) /\
               read X4 s = a /\ read X17 s = word_add a (word 2) /\
               read X7 s = word(start + 2 * len) /\
               read X10 s = word(start + 3 * len) /\
               read X11 s = word(k + 1) /\
               read X6 s = word_zx(word_sx z:int32) /\
               read X12 s = word(2 * len) /\ read X13 s = word len /\
               read X15 s = word len /\
               read X8 s = word 4294963967 /\ read X9 s = word 4294963969 /\
               read X14 s = word zetas /\ read X16 s = w16 /\
               read X18 s = word 1 /\ read X30 s = word 256 /\
               read Q5 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
               read Q6 s = word 0xf301f301f301f301f301f301f301f301 /\
               read Q7 s = word 0xf301f301f301f301 /\
               read Q16 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        ntt_block_c z start len m i))
          (MAYCHANGE [PC; X0; X1; X2; X3; X5; X7; X10; X11; X19; X20; X21] ,,
           MAYCHANGE [Q0; Q1; Q2; Q3; Q4] ,, MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(a,512)])` in
  let vs,body = strip_forall tm in
  list_mk_forall(vs,subst [hyp,`HYP:bool`] body);;

let NTT_DBLOCK_HALF_TAC ath =
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[ath] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MONTRED_NEON_SCALAR]) THEN
  ASM_REWRITE_TAC[ntt_fqmul_c];;

let MLKEM_NATIVE_POLY_NTT_GCC12_O3_DBLOCK_STMT =
  ntt_block_goal
   `len = 4 /\ ~(val(word_add (a:int64) (word(2 * start))) + 24 < 2 EXP 64)`;;

let MLKEM_NATIVE_POLY_NTT_GCC12_O3_DBLOCK =
  assume_spec MLKEM_NATIVE_POLY_NTT_GCC12_O3_DBLOCK_STMT;;

(*** A block of 4 + 4 coefficients, wherever it is ***)

let MLKEM_NATIVE_POLY_NTT_GCC12_O3_BLOCK4_STMT =
  ntt_block_goal `len = 4`;;

let MLKEM_NATIVE_POLY_NTT_GCC12_O3_BLOCK4 =
  assume_spec MLKEM_NATIVE_POLY_NTT_GCC12_O3_BLOCK4_STMT;;

(* ------------------------------------------------------------------------- *)
(* One layer, with the blocks in a loop (except for the first layer).        *)
(* ------------------------------------------------------------------------- *)

(*** Prepare a load of zeta number n using UXTW indexing ***)

let ZETA_UXTW_TAC n =
  MP_TAC(SPEC n VAL_WORD_ZX_UXTW) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC] THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && free_in `mlk_zetas` (concl th)
    then MP_TAC(SPEC n th) else failwith "") THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC];;

(*** Assertions at the block head and block end for layer l, block b ***)

let ntt_blockhead_tm,ntt_blockend_tm =
  let headtm =
   `\s. aligned_bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O3_mc /\
        read X4 s = a /\ read X17 s = word_add a (word 2) /\
        read X7 s = word(2 * LEN * B) /\
        read X10 s = word(2 * LEN * B + LEN) /\
        read X11 s = word(2 EXP L + B) /\
        read X6 s =
        word_zx(word_sx(iword(EL (2 EXP L + B) mlk_zetas):int16):int32) /\
        read X12 s = word(2 * LEN) /\ read X13 s = word LEN /\
        read X15 s = word LEN /\
        read X8 s = word 4294963967 /\ read X9 s = word 4294963969 /\
        read X14 s = word zetas /\ read X16 s = word(L + 1) /\
        read X18 s = word 1 /\ read X30 s = word 256 /\
        read Q5 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
        read Q6 s = word 0xf301f301f301f301f301f301f301f301 /\
        read Q7 s = word 0xf301f301f301f301 /\
        read Q16 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
        (!k. k < 128
             ==> read(memory :> bytes16(word_add (word zetas)
                                                 (word(2 * k)))) s =
                 iword(EL k mlk_zetas)) /\
        (!i. i < 256
             ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                 ntt_blocks_c L B r i)`
  and endtm =
   `\s. aligned_bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O3_mc /\
        read X4 s = a /\ read X17 s = word_add a (word 2) /\
        read X7 s = word(2 * LEN * B) /\
        read X10 s = word(2 * LEN * B + LEN) /\
        read X11 s = word(2 EXP L + B) /\
        read X12 s = word(2 * LEN) /\ read X13 s = word LEN /\
        read X15 s = word LEN /\
        read X8 s = word 4294963967 /\ read X9 s = word 4294963969 /\
        read X14 s = word zetas /\ read X16 s = word(L + 1) /\
        read X18 s = word 1 /\ read X30 s = word 256 /\
        read Q5 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
        read Q6 s = word 0xf301f301f301f301f301f301f301f301 /\
        read Q7 s = word 0xf301f301f301f301 /\
        read Q16 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
        (!k. k < 128
             ==> read(memory :> bytes16(word_add (word zetas)
                                                 (word(2 * k)))) s =
                 iword(EL k mlk_zetas)) /\
        (!i. i < 256
             ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                 ntt_blocks_c L B r i)` in
  let mk tm l b =
    let len = mk_small_numeral(1 lsl (7 - l)) in
    let tm' = subst [mk_small_numeral l,`L:num`; len,`LEN:num`; b,`B:num`]
                    tm in
    rhs(concl(NUM_REDUCE_CONV tm')) in
  (fun l b -> mk headtm l b),(fun l b -> mk endtm l b);;

(*** Apply a block lemma at the head of block b of layer l: the vector
 *** block for the first five layers, with 8 * n coefficients in each half
 *** for n = 2^(4 - l), then the block of 4 + 4 and the scalar block of
 *** 2 + 2 coefficients
 ***)

let NTT_BLOCK_TAC l b =
  let red t =
    rhs(concl(NUM_REDUCE_CONV(subst
     [mk_small_numeral l,`L:num`; mk_small_numeral(1 lsl (7 - l)),`LEN:num`;
      b,`B:num`] t))) in
  let th =
    if l <= 4 then
      SPECL [`a:int64`; `zetas:num`; `pc:num`;
             red `iword(EL (2 EXP L + B) mlk_zetas):int16`;
             red `2 * LEN * B`; mk_small_numeral(1 lsl (4 - l));
             red `2 EXP L + B`; red `ntt_blocks_c L B r`;
             red `word(L + 1):int64`]
            MLKEM_NATIVE_POLY_NTT_GCC12_O3_VBLOCK
    else
      SPECL [`a:int64`; `zetas:num`; `pc:num`;
             red `iword(EL (2 EXP L + B) mlk_zetas):int16`;
             red `2 * LEN * B`; red `LEN:num`;
             red `2 EXP L + B`; red `ntt_blocks_c L B r`;
             red `word(L + 1):int64`]
            (if l = 5 then MLKEM_NATIVE_POLY_NTT_GCC12_O3_BLOCK4
             else MLKEM_NATIVE_POLY_NTT_GCC12_O3_SBLOCK) in
  let sth = CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ADD1]
    (INST [mk_small_numeral l,`l:num`; b,`b:num`]
          (SPEC_ALL(CONJUNCT2 ntt_blocks_c)))) in
  MP_TAC th THEN ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(ENSURES_WEAKEN_TAC o CONV_RULE NUM_REDUCE_CONV) THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[sth] THEN
    REPEAT CONJ_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC];;

(*** The layer head, setting up the registers for the first block ***)

let NTT_LAYERHEAD_TAC l =
  ENSURES_SEQUENCE_TAC `pc + mlkem_poly_ntt_loop2`
   (ntt_blockhead_tm l `0`) THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O3_EXEC (1--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[ntt_blocks_c] THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(*** The exit from the block loop at the end of the layer ***)

let NTT_LAYEREXIT_TAC =
  ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O3_EXEC (1--1) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O3_EXEC (2--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(*** The whole layer l (number of layers done before it) ***)

let NTT_LAYER_TAC l =
  NTT_LAYERHEAD_TAC l THEN
  ENSURES_SEQUENCE_TAC `pc + mlkem_poly_ntt_loop2_test1`
   (ntt_blockend_tm l `1`) THEN
  CONJ_TAC THENL
   [NTT_BLOCK_TAC l `0`;
    if l = 0 then NTT_LAYEREXIT_TAC else
    ENSURES_WHILE_UP_TAC (mk_small_numeral(1 lsl l - 1))
      `pc + mlkem_poly_ntt_loop2_test1` `pc + mlkem_poly_ntt_loop2_test1`
      (mk_abs(`i:num`,ntt_blockend_tm l `i + 1`)) THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV;
      ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ENSURES_SEQUENCE_TAC `pc + mlkem_poly_ntt_loop2` (ntt_blockhead_tm l
       `i + 1`) THEN
      CONJ_TAC THENL
       [ENSURES_INIT_TAC "s0" THEN
        ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O3_EXEC (1--1) THEN
        W32_DECIDE_FLAGS_TAC THEN
        ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O3_EXEC (2--2) THEN
        ZETA_UXTW_TAC
         (rhs(concl(NUM_REDUCE_CONV
           (subst [mk_small_numeral l,`L:num`] `2 EXP L + i + 1`)))) THEN
        ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O3_EXEC (3--4) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
        NTT_BLOCK_TAC l `i + 1`];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[];
      NTT_LAYEREXIT_TAC]];;

let ntt_layer_goal l =
  let tm =
  `!a zetas pc r.
     ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size);
                                   (word zetas,256)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O3_mc /\
               read PC s = word(pc + mlkem_poly_ntt_loop1) /\
               read X11 s = word L /\
               read X6 s =
               word_zx(word_sx(iword(EL (2 EXP L) mlk_zetas):int16):int32) /\
               read X4 s = a /\ read X17 s = word_add a (word 2) /\
               read X8 s = word 4294963967 /\ read X9 s = word 4294963969 /\
               read X14 s = word zetas /\
               read X18 s = word 1 /\ read X30 s = word 256 /\
               read Q5 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
               read Q6 s = word 0xf301f301f301f301f301f301f301f301 /\
               read Q7 s = word 0xf301f301f301f301 /\
               read Q16 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        r i))
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O3_mc /\
               read PC s = word(pc + mlkem_poly_ntt_loop2_exit) /\
               read X16 s = word(L + 1) /\
               read X4 s = a /\ read X17 s = word_add a (word 2) /\
               read X8 s = word 4294963967 /\ read X9 s = word 4294963969 /\
               read X14 s = word zetas /\
               read X18 s = word 1 /\ read X30 s = word 256 /\
               read Q5 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
               read Q6 s = word 0xf301f301f301f301f301f301f301f301 /\
               read Q7 s = word 0xf301f301f301f301 /\
               read Q16 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        ntt_blocks_c L (2 EXP L) r i))
          (MAYCHANGE [PC; X0; X1; X2; X3; X5; X6; X7; X10; X11; X12; X13;
                      X15; X16; X19; X20; X21] ,,
           MAYCHANGE [Q0; Q1; Q2; Q3; Q4] ,, MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(a,512)])` in
  rhs(concl(NUM_REDUCE_CONV(subst [mk_small_numeral l,`L:num`] tm)));;

let NTT_LAYER_PROOF_TAC l =
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  NTT_LAYER_TAC l;;

let MLKEM_NATIVE_POLY_NTT_GCC12_O3_LAYERS = assuming_proofs (fun () ->
  map (fun l -> prove(ntt_layer_goal l,NTT_LAYER_PROOF_TAC l)) (0--6));;


(* ------------------------------------------------------------------------- *)
(* The computation of the C code gives the NTT, within the same bounds as    *)
(* the hand-written kernel.                                                  *)
(* ------------------------------------------------------------------------- *)

let NTT_BLOCKS_C_CLOSED_STMT =
  `!l b r i.
     ntt_blocks_c l b r i =
     if i < 2 * 2 EXP (7 - l) * b
     then let z = iword(EL (2 EXP l + i DIV (2 * 2 EXP (7 - l))) mlk_zetas) in
          if i MOD (2 * 2 EXP (7 - l)) < 2 EXP (7 - l)
          then word_add (r i) (ntt_fqmul_c z (r(i + 2 EXP (7 - l))))
          else word_sub (r(i - 2 EXP (7 - l))) (ntt_fqmul_c z (r i))
     else r i`;;

let NTT_BLOCKS_C_CLOSED = assume_spec NTT_BLOCKS_C_CLOSED_STMT;;

let NTT_LAYERS_C_STEP_STMT =
  `!l x i.
     l < 7 /\ i < 256
     ==> ntt_layers_c (SUC l) x i =
         let z = iword(EL (2 EXP l + i DIV (2 * 2 EXP (7 - l))) mlk_zetas) in
         if i MOD (2 * 2 EXP (7 - l)) < 2 EXP (7 - l)
         then word_add (ntt_layers_c l x i)
                       (ntt_fqmul_c z (ntt_layers_c l x (i + 2 EXP (7 - l))))
         else word_sub (ntt_layers_c l x (i - 2 EXP (7 - l)))
                       (ntt_fqmul_c z (ntt_layers_c l x i))`;;

let NTT_LAYERS_C_STEP = assume_spec NTT_LAYERS_C_STEP_STMT;;

let MLK_ZETAS_ELS =
  map (fun k -> (REWRITE_CONV[mlk_zetas] THENC EL_CONV)
                 (mk_comb(mk_comb(`EL:num->int list->int`,mk_small_numeral k),
                          `mlk_zetas`))) (0--127);;

let NTT_LAYER_EQUATION =
  let conv =
    NUM_REDUCE_CONV THENC TOP_DEPTH_CONV let_CONV THENC
    REWRITE_CONV(CONJUNCT1 ntt_layers_c :: MLK_ZETAS_ELS) THENC
    ONCE_DEPTH_CONV WORD_IWORD_CONV THENC REWRITE_CONV[ntt_fqmul_c] THENC
    DEPTH_CONV WORD_RED_CONV in
  fun l i ->
    let th = SPECL [mk_small_numeral l; `x:num->int16`; mk_small_numeral i]
                   NTT_LAYERS_C_STEP in
    let th' = MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))) in
    CONV_RULE(BINOP_CONV conv) th';;

(*** All the layer equations, in the order of the layers ***)

let NTT_LAYER_EQUATIONS =
  map (fun (l,i) -> SYM(NTT_LAYER_EQUATION l i))
      (List.concat (map (fun l -> map (fun i -> (l,i)) (0--255)) (0--6)));;

let NTT_FINAL_TAC lfn =
  W(fun (asl,w) ->
    let tm = find_term (can (term_match [] `ntt_layers_c 7 x i`)) w in
    let th = apply lfn tm in
    if not(fst(dest_const(repeat rator w)) = "int_le") then
      MP_TAC(CONJUNCT1 th) THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_TRANS) THEN
      CONV_TAC(ONCE_DEPTH_CONV FORWARD_NTT_CONV) THEN
      REWRITE_TAC[GSYM INT_REM_EQ; o_THM] THEN CONV_TAC INT_REM_DOWN_CONV THEN
      REWRITE_TAC[INT_REM_EQ] THEN INT_LINEAR_CONG_TAC
    else
      MP_TAC(CONJUNCT2 th) THEN INT_ARITH_TAC);;

let NTT_LAYERS_C_CORRECT_STMT =
  `!x. (!i. i < 256 ==> abs(ival(x i)) <= &8191)
       ==> !i. i < 256
               ==> (ival(ntt_layers_c 7 x i) == forward_ntt (ival o x) i)
                   (mod &3329) /\
                   abs(ival(ntt_layers_c 7 x i)) <= &23594`;;

let NTT_LAYERS_C_CORRECT = assume_spec NTT_LAYERS_C_CORRECT_STMT;;


(* ------------------------------------------------------------------------- *)
(* The layers compute the C version of the NTT.                              *)
(* ------------------------------------------------------------------------- *)

(*** Assertions at the layer head and layer end for layer l ***)

let ntt_layerhead_tm,ntt_layerend_tm =
  let headtm =
   `\s. aligned_bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O3_mc /\
        read X11 s = word L /\
        read X6 s =
        word_zx(word_sx(iword(EL (2 EXP L) mlk_zetas):int16):int32) /\
        read X4 s = a /\ read X17 s = word_add a (word 2) /\
        read X8 s = word 4294963967 /\ read X9 s = word 4294963969 /\
        read X14 s = word zetas /\
        read X18 s = word 1 /\ read X30 s = word 256 /\
        read Q5 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
        read Q6 s = word 0xf301f301f301f301f301f301f301f301 /\
        read Q7 s = word 0xf301f301f301f301 /\
        read Q16 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
        (!k. k < 128
             ==> read(memory :> bytes16(word_add (word zetas)
                                                 (word(2 * k)))) s =
                 iword(EL k mlk_zetas)) /\
        (!i. i < 256
             ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                 ntt_layers_c L x i)`
  and endtm =
   `\s. aligned_bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O3_mc /\
        read X16 s = word(L + 1) /\
        read X4 s = a /\ read X17 s = word_add a (word 2) /\
        read X8 s = word 4294963967 /\ read X9 s = word 4294963969 /\
        read X14 s = word zetas /\
        read X18 s = word 1 /\ read X30 s = word 256 /\
        read Q5 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
        read Q6 s = word 0xf301f301f301f301f301f301f301f301 /\
        read Q7 s = word 0xf301f301f301f301 /\
        read Q16 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
        (!k. k < 128
             ==> read(memory :> bytes16(word_add (word zetas)
                                                 (word(2 * k)))) s =
                 iword(EL k mlk_zetas)) /\
        (!i. i < 256
             ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                 ntt_layers_c (L + 1) x i)` in
  let mk tm l =
    let tm' = subst [mk_small_numeral l,`L:num`] tm in
    rhs(concl(NUM_REDUCE_CONV tm')) in
  (fun l -> mk headtm l),(fun l -> mk endtm l);;

(*** Apply the lemma for layer l at its head ***)

let NTT_LAYER_APPLY_TAC l =
  let th = SPECL [`a:int64`; `zetas:num`; `pc:num`;
                  rhs(concl(NUM_REDUCE_CONV(subst [mk_small_numeral l,`L:num`]
                     `ntt_layers_c L x`)))]
                 (el l MLKEM_NATIVE_POLY_NTT_GCC12_O3_LAYERS) in
  let sth = CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ADD1]
    (INST [mk_small_numeral l,`l:num`]
          (SPEC_ALL(CONJUNCT2 ntt_layers_c)))) in
  MP_TAC th THEN ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN ENSURES_WEAKEN_TAC THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[sth];
    REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC];;

(*** Going from the end of layer l to the head of the next layer ***)

let NTT_LAYERBACK_TAC l =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O3_EXEC (1--1) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O3_EXEC (2--4) THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && free_in `mlk_zetas` (concl th)
    then MP_TAC(CONV_RULE NUM_REDUCE_CONV
                  (SPEC (mk_small_numeral(1 lsl (l + 1))) th))
    else failwith "") THEN
  REWRITE_TAC[ARITH] THEN DISCH_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O3_EXEC (5--6) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);;

let MLKEM_NATIVE_POLY_NTT_GCC12_O3_ALL_LAYERS_STMT =
  `!a zetas (x:num->int16) pc.
    ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size); (word zetas,256)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_gcc12_O3_mc /\
           read PC s = word(pc + mlkem_poly_ntt_loop1) /\
           read X11 s = word 0 /\
           read X6 s =
           word_zx(word_sx(iword(EL 1 mlk_zetas):int16):int32) /\
           read X4 s = a /\ read X17 s = word_add a (word 2) /\
           read X8 s = word 4294963967 /\ read X9 s = word 4294963969 /\
           read X14 s = word zetas /\
           read X18 s = word 1 /\ read X30 s = word 256 /\
           read Q5 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
           read Q6 s = word 0xf301f301f301f301f301f301f301f301 /\
           read Q7 s = word 0xf301f301f301f301 /\
           read Q16 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
           (!k. k < 128
                ==> read(memory :> bytes16(word_add (word zetas)
                                                    (word(2 * k)))) s =
                    iword(EL k mlk_zetas)) /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    x i))
      (\s. read PC s = word(pc + mlkem_poly_ntt_loop1_exit) /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    ntt_layers_c 7 x i))
      (MAYCHANGE [PC; X0; X1; X2; X3; X5; X6; X7; X10; X11; X12; X13;
                  X15; X16; X19; X20; X21] ,,
       MAYCHANGE [Q0; Q1; Q2; Q3; Q4] ,, MAYCHANGE SOME_FLAGS ,,
       MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_NTT_GCC12_O3_ALL_LAYERS =
  assume_spec MLKEM_NATIVE_POLY_NTT_GCC12_O3_ALL_LAYERS_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

(*** The vector of 3329^-1 mod 2^16, as a Q and a D register, and the table
 *** of zetas in the image
 ***)

let MLKEM_NATIVE_POLY_NTT_GCC12_O3_CONSTANTS =
  map (MLKEM_NATIVE_IMAGE_CONST_RULE (layout "mlkem_poly_ntt_consts"))
      [128; 64];;

let MLKEM_NATIVE_POLY_NTT_GCC12_O3_ZETAS_IN_IMAGE =
  MLKEM_NATIVE_IMAGE_DATA_RULE mlk_zetas_data (layout "rodata_mlk_zetas");;

let MLKEM_NATIVE_POLY_NTT_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a (x:num->int16) pc stackpointer returnaddress.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    aligned 16 stackpointer /\
    nonoverlapping (a,512) (word_sub stackpointer (word 32),32) /\
    ALLPAIRS nonoverlapping
     [(a,512); (word_sub stackpointer (word 32),32)]
     [(word pc,libmlkem_size)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_gcc12_O3_mc /\
           read PC s = word (pc + mlkem_poly_ntt) /\
           read SP s = stackpointer /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [a] s /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    x i))
      (\s. read PC s = returnaddress /\
           ((!i. i < 256 ==> abs(ival(x i)) <= &8191)
            ==> !i. i < 256
                    ==> let zi =
                          read(memory :> bytes16(word_add a (word(2 * i)))) s
                        in (ival zi == forward_ntt (ival o x) i) (mod &3329) /\
                           abs(ival zi) <= &23594))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
       MAYCHANGE [memory :> bytes(a,512);
                  memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLKEM_NATIVE_POLY_NTT_GCC12_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_NTT_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. This follows the structure of the  *)
(* correctness proof, with the events of a block and of each layer given by  *)
(* functions obtained from the corresponding lemmas.                         *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The frame of the lemmas for the blocks and layers, which also use X19,
 *** X20 and X21, saved on the stack by the whole function
 ***)

let NTT_SAFE_FRAME_TAC =
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC;;

(*** Simulation of a short piece of straight-line code with flags ***)

let NTT_SAFE_SIM_TAC pre_tac n =
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN pre_tac THEN
  MAP_EVERY (fun i ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O3_EXEC [i] THEN
    TRY W32_DECIDE_FLAGS_TAC) (1--n) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  REPEAT(CONJ_TAC THENL
   [REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    (NTT_SMALL_TAC ORELSE ASM_ARITH_TAC ORELSE
     (AP_TERM_TAC THEN ASM_ARITH_TAC));
    ALL_TAC]) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** One block of the first five layers ***)

let MLKEM_NATIVE_POLY_NTT_GCC12_O3_VBLOCK_SAFE_STMT =
  `exists f_ev_blk.
   forall e a zetas pc start n k w16 sp x19v x20v x21v ra.
     ALL (nonoverlapping (a,512))
         [(word pc,libmlkem_size); (word zetas,256); (sp,32)] /\
     1 <= n /\ start + 16 * n <= 256 /\ k < 256
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O3_mc /\
               read PC s = word(pc + mlkem_poly_ntt_loop2) /\
               read X4 s = a /\ read X17 s = word_add a (word 2) /\
               read X7 s = word start /\ read X10 s = word(start + 8 * n) /\
               read X11 s = word k /\
               read X12 s = word(16 * n) /\ read X13 s = word(8 * n) /\
               read X15 s = word(8 * n) /\
               read X14 s = word zetas /\ read X16 s = w16 /\
               read X18 s = word 1 /\ read X30 s = word 256 /\
               read SP s = sp /\
               read(memory :> bytes64 sp) s = x19v /\
               read(memory :> bytes64(word_add sp (word 8))) s = x20v /\
               read(memory :> bytes64(word_add sp (word 16))) s = x21v /\
               read(memory :> bytes64(word_add sp (word 24))) s = ra /\
               read events s = e)
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O3_mc /\
               read PC s = word(pc + mlkem_poly_ntt_loop2_test1) /\
               read X4 s = a /\ read X17 s = word_add a (word 2) /\
               read X7 s = word(start + 16 * n) /\
               read X10 s = word(start + 24 * n) /\
               read X11 s = word(k + 1) /\
               read X12 s = word(16 * n) /\ read X13 s = word(8 * n) /\
               read X15 s = word(8 * n) /\
               read X14 s = word zetas /\ read X16 s = w16 /\
               read X18 s = word 1 /\ read X30 s = word 256 /\
               read SP s = sp /\
               read(memory :> bytes64 sp) s = x19v /\
               read(memory :> bytes64(word_add sp (word 8))) s = x20v /\
               read(memory :> bytes64(word_add sp (word 16))) s = x21v /\
               read(memory :> bytes64(word_add sp (word 24))) s = ra /\
               exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_ev_blk a zetas pc start n /\
                 memaccess_inbounds e2 [a,512; word zetas,256] [a,512])
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [X18; X19; X20; X21] ,,
           MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_NTT_GCC12_O3_VBLOCK_SAFE =
  assume_spec MLKEM_NATIVE_POLY_NTT_GCC12_O3_VBLOCK_SAFE_STMT;;

(*** The blocks of the last two layers ***)

let ntt_sblock_safe_goal hyp =
  let tm =
  `exists f_ev_blk.
   forall e a zetas pc start len k w16 sp x19v x20v x21v ra.
     ALL (nonoverlapping (a,512))
         [(word pc,libmlkem_size); (word zetas,256); (sp,32)] /\
     HYP /\ start + 2 * len <= 256 /\ k < 256
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O3_mc /\
               read PC s = word(pc + mlkem_poly_ntt_loop2) /\
               read X4 s = a /\ read X17 s = word_add a (word 2) /\
               read X7 s = word start /\ read X10 s = word(start + len) /\
               read X11 s = word k /\
               read X12 s = word(2 * len) /\ read X13 s = word len /\
               read X15 s = word len /\
               read X14 s = word zetas /\ read X16 s = w16 /\
               read X18 s = word 1 /\ read X30 s = word 256 /\
               read SP s = sp /\
               read(memory :> bytes64 sp) s = x19v /\
               read(memory :> bytes64(word_add sp (word 8))) s = x20v /\
               read(memory :> bytes64(word_add sp (word 16))) s = x21v /\
               read(memory :> bytes64(word_add sp (word 24))) s = ra /\
               read events s = e)
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O3_mc /\
               read PC s = word(pc + mlkem_poly_ntt_loop2_test1) /\
               read X4 s = a /\ read X17 s = word_add a (word 2) /\
               read X7 s = word(start + 2 * len) /\
               read X10 s = word(start + 3 * len) /\
               read X11 s = word(k + 1) /\
               read X12 s = word(2 * len) /\ read X13 s = word len /\
               read X15 s = word len /\
               read X14 s = word zetas /\ read X16 s = w16 /\
               read X18 s = word 1 /\ read X30 s = word 256 /\
               read SP s = sp /\
               read(memory :> bytes64 sp) s = x19v /\
               read(memory :> bytes64(word_add sp (word 8))) s = x20v /\
               read(memory :> bytes64(word_add sp (word 16))) s = x21v /\
               read(memory :> bytes64(word_add sp (word 24))) s = ra /\
               exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_ev_blk a zetas pc start len /\
                 memaccess_inbounds e2 [a,512; word zetas,256] [a,512])
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [X18; X19; X20; X21] ,,
           MAYCHANGE [memory :> bytes(a,512)])` in
  let f,b = dest_exists tm in
  let vs,body = strip_forall b in
  mk_exists(f,list_mk_forall(vs,subst [hyp,`HYP:bool`] body));;

(*** The steps from the head of the block to the scalar loop, directly for
 *** 2 + 2 coefficients, and after the check for 4 + 4
 ***)

let NTT_SBLOCK_HEAD_SAFE_TAC long =
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O3_EXEC (1--2) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O3_EXEC (3--6) THEN
  REG_SMALL_TAC `X20` `word len:int64` THEN
  REG_SMALL_TAC `X19` `word(len - 1):int64` THEN
  REG_SMALL_TAC `X1` `word start:int64` THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O3_EXEC (7--7) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O3_EXEC (8--8) THEN
  (if not long then ALL_TAC else
   ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O3_EXEC (9--18) THEN
   REG_SMALL_TAC `X0` `word_add a (word(2 * start + 24)):int64` THEN
   REG_SMALL_TAC `X21` `word_add a (word(2 * start + 16)):int64` THEN
   REG_SMALL_TAC `X2` `word_add a (word(2 * start)):int64` THEN
   REG_SMALL_TAC `X3` `word_add a (word(2 * start + 8)):int64` THEN
   ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O3_EXEC (19--20) THEN
   MP_TAC(SPECL [`a:int64`; `2 * start`] NTT_ALIAS_SCALAR) THEN
   ANTS_TAC THENL
    [ASM_ARITH_TAC;
     DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
   ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O3_EXEC (21--21)) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O3_EXEC
   (if long then 22--26 else 9--13) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  REPEAT(CONJ_TAC THENL [NTT_SMALL_TAC; ALL_TAC]) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let NTT_SBLOCK_SAFE_TAC long =
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (zetas:num) (pc:num) (start:num) (len:num).
      APPEND (f_ev_blkend a zetas pc start len)
        (APPEND (ENUMERATEL len
                   (\j. f_ev_bfly a zetas pc start len j))
                (f_ev_blkhead a zetas pc start len))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  NTT_SAFE_FRAME_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `len:num` `pc + mlkem_poly_ntt_loop3`
   `pc + mlkem_poly_ntt_loop3_exit`
   `\j s. read X1 s = word_add a (word(2 * (start + j))) /\
          read X19 s = word_add a (word(2 * (start + len))) /\
          read X5 s = word len /\
          read X4 s = a /\ read X17 s = word_add a (word 2) /\
          read X7 s = word start /\ read X10 s = word(start + len) /\
          read X11 s = word(k + 1) /\
          read X12 s = word(2 * len) /\ read X13 s = word len /\
          read X15 s = word len /\
          read X14 s = word zetas /\ read X16 s = w16 /\
          read X18 s = word 1 /\ read X30 s = word 256 /\
          read SP s = sp /\
          read(memory :> bytes64 sp) s = x19v /\
          read(memory :> bytes64(word_add sp (word 8))) s = x20v /\
          read(memory :> bytes64(word_add sp (word 16))) s = x21v /\
          read(memory :> bytes64(word_add sp (word 24))) s = ra` THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;

    NTT_SBLOCK_HEAD_SAFE_TAC long;

    (*** The scalar loop body, one butterfly, and the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    SUBGOAL_THEN `val(word len:int64) = len` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O3_EXEC (1--12) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_add (word_add a (word x)) (word y):int64 =
      word_add a (word(x + y))`]) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O3_EXEC (13--13) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O3_EXEC (14--14) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    W(fun (asl,w) ->
      let t = find_term (can (term_match []
               `~(2 * (start + l) = 2 * (start + i) + 2)`)) w in
      let l = rand(rand(lhand(rand t))) in
      SUBGOAL_THEN (mk_eq(t,mk_binop `(<):num->num->bool` `i + 1` l))
       SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The end of the block ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O3_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL [NTT_SMALL_TAC; ALL_TAC]) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let MLKEM_NATIVE_POLY_NTT_GCC12_O3_SBLOCK2_SAFE_STMT =
  ntt_sblock_safe_goal `len = 2`;;

let MLKEM_NATIVE_POLY_NTT_GCC12_O3_SBLOCK2_SAFE =
  assume_spec MLKEM_NATIVE_POLY_NTT_GCC12_O3_SBLOCK2_SAFE_STMT;;

let MLKEM_NATIVE_POLY_NTT_GCC12_O3_SBLOCK4_SAFE_STMT =
  ntt_sblock_safe_goal
   `len = 4 /\ val(word_add (a:int64) (word(2 * start))) + 24 < 2 EXP 64`;;

let MLKEM_NATIVE_POLY_NTT_GCC12_O3_SBLOCK4_SAFE =
  assume_spec MLKEM_NATIVE_POLY_NTT_GCC12_O3_SBLOCK4_SAFE_STMT;;

let MLKEM_NATIVE_POLY_NTT_GCC12_O3_DBLOCK_SAFE_STMT =
  ntt_sblock_safe_goal
   `len = 4 /\ ~(val(word_add (a:int64) (word(2 * start))) + 24 < 2 EXP 64)`;;

let MLKEM_NATIVE_POLY_NTT_GCC12_O3_DBLOCK_SAFE =
  assume_spec MLKEM_NATIVE_POLY_NTT_GCC12_O3_DBLOCK_SAFE_STMT;;

(*** A block of 4 + 4 coefficients, wherever it is ***)

let MLKEM_NATIVE_POLY_NTT_GCC12_O3_BLOCK4_SAFE_STMT =
  ntt_sblock_safe_goal `len = 4`;;

let MLKEM_NATIVE_POLY_NTT_GCC12_O3_BLOCK4_SAFE =
  assume_spec MLKEM_NATIVE_POLY_NTT_GCC12_O3_BLOCK4_SAFE_STMT;;

let NTT_GCC12_O3_VBLOCK_EVENTS =
  new_specification ["ntt_gcc12_O3_vblock_events"]
                    MLKEM_NATIVE_POLY_NTT_GCC12_O3_VBLOCK_SAFE;;

let NTT_GCC12_O3_BLOCK4_EVENTS =
  new_specification ["ntt_gcc12_O3_block4_events"]
                    MLKEM_NATIVE_POLY_NTT_GCC12_O3_BLOCK4_SAFE;;

let NTT_GCC12_O3_SBLOCK2_EVENTS =
  new_specification ["ntt_gcc12_O3_sblock2_events"]
                    MLKEM_NATIVE_POLY_NTT_GCC12_O3_SBLOCK2_SAFE;;

(*** One layer, for each of the seven layers ***)

let lsafe_goal l =
  let tm =
  `exists f_ev_lay.
    forall e a zetas pc sp x19v x20v x21v ra.
     ALL (nonoverlapping (a,512))
         [(word pc,libmlkem_size); (word zetas,256); (sp,32)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O3_mc /\
               read PC s = word(pc + mlkem_poly_ntt_loop1) /\
               read X11 s = word L /\
               read X4 s = a /\ read X17 s = word_add a (word 2) /\
               read X14 s = word zetas /\
               read X18 s = word 1 /\ read X30 s = word 256 /\
               read SP s = sp /\
               read(memory :> bytes64 sp) s = x19v /\
               read(memory :> bytes64(word_add sp (word 8))) s = x20v /\
               read(memory :> bytes64(word_add sp (word 16))) s = x21v /\
               read(memory :> bytes64(word_add sp (word 24))) s = ra /\
               read events s = e)
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_O3_mc /\
               read PC s = word(pc + mlkem_poly_ntt_loop2_exit) /\
               read X16 s = word(L + 1) /\
               read X4 s = a /\ read X17 s = word_add a (word 2) /\
               read X14 s = word zetas /\
               read X18 s = word 1 /\ read X30 s = word 256 /\
               read SP s = sp /\
               read(memory :> bytes64 sp) s = x19v /\
               read(memory :> bytes64(word_add sp (word 8))) s = x20v /\
               read(memory :> bytes64(word_add sp (word 16))) s = x21v /\
               read(memory :> bytes64(word_add sp (word 24))) s = ra /\
               exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_ev_lay a zetas pc /\
                 memaccess_inbounds e2 [a,512; word zetas,256] [a,512])
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [X18; X19; X20; X21] ,,
           MAYCHANGE [memory :> bytes(a,512)])` in
  rhs(concl(NUM_REDUCE_CONV(subst [mk_small_numeral l,`L:num`] tm)));;

(*** The events of block b of layer l, from the block lemmas ***)

let ntt_blk_events l b =
  let len = 1 lsl (7 - l) in
  let start = rhs(concl(NUM_REDUCE_CONV(subst
                [mk_small_numeral len,`LEN:num`; b,`B:num`] `2 * LEN * B`))) in
  if l <= 4 then
    list_mk_comb(`ntt_gcc12_O3_vblock_events`,
      [`a:int64`; `zetas:num`; `pc:num`; start; mk_small_numeral(len / 8)])
  else
    list_mk_comb((if l = 5 then `ntt_gcc12_O3_block4_events`
                  else `ntt_gcc12_O3_sblock2_events`),
      [`a:int64`; `zetas:num`; `pc:num`; start; mk_small_numeral len]);;

(*** The event template for layer l ***)

let lsafe_template l =
  let app x y = list_mk_icomb "APPEND" [x;y]
  and fev n args =
    list_mk_comb(mk_var(n,itlist (mk_fun_ty o type_of) args
                                 `:(uarch_event)list`),args) in
  let base = [`a:int64`; `zetas:num`; `pc:num`] in
  let blk0 = app (fev "f_ev_ltest0" base)
                 (app (ntt_blk_events l `0`) (fev "f_ev_lhead" base)) in
  let body =
    if l = 0 then blk0 else
    app (fev "f_ev_lexit" base)
     (app (mk_icomb(mk_icomb(`ENUMERATEL:num->(num->(uarch_event)list)->
                                          (uarch_event)list`,
                              mk_small_numeral(1 lsl l - 1)),
           mk_abs(`i:num`,
             app (fev "f_ev_ltest" (base @ [`i:num`]))
                 (app (ntt_blk_events l `i + 1`)
                      (fev "f_ev_lzeta" (base @ [`i:num`]))))))
          blk0) in
  list_mk_abs(base,body);;

(*** The block lemma for block b of layer l ***)

let ntt_block_events_inst l b ev =
  let len = 1 lsl (7 - l) in
  let red t = rhs(concl(NUM_REDUCE_CONV(subst
     [mk_small_numeral l,`L:num`; mk_small_numeral len,`LEN:num`;
      b,`B:num`] t))) in
  let th =
    if l <= 4 then NTT_GCC12_O3_VBLOCK_EVENTS
    else if l = 5 then NTT_GCC12_O3_BLOCK4_EVENTS
    else NTT_GCC12_O3_SBLOCK2_EVENTS in
  SPECL [ev; `a:int64`; `zetas:num`; `pc:num`;
         red `2 * LEN * B`;
         (if l <= 4 then mk_small_numeral(len / 8) else red `LEN:num`);
         red `2 EXP L + B`; red `word(L + 1):int64`;
         `sp:int64`; `x19v:int64`; `x20v:int64`; `x21v:int64`; `ra:int64`] th;;

(*** Register state at the block head and block end (b blocks done) ***)

let lsafe_blockhead_tm,lsafe_blockend_tm =
  let headtm =
   `\s. read X4 s = a /\ read X17 s = word_add a (word 2) /\
        read X7 s = word(2 * LEN * B) /\
        read X10 s = word(2 * LEN * B + LEN) /\
        read X11 s = word(2 EXP L + B) /\
        read X12 s = word(2 * LEN) /\ read X13 s = word LEN /\
        read X15 s = word LEN /\
        read X14 s = word zetas /\ read X16 s = word(L + 1) /\
        read X18 s = word 1 /\ read X30 s = word 256 /\
        read SP s = sp /\
        read(memory :> bytes64 sp) s = x19v /\
        read(memory :> bytes64(word_add sp (word 8))) s = x20v /\
        read(memory :> bytes64(word_add sp (word 16))) s = x21v /\
        read(memory :> bytes64(word_add sp (word 24))) s = ra` in
  let mk l b =
    rhs(concl(NUM_REDUCE_CONV(subst
     [mk_small_numeral l,`L:num`; mk_small_numeral(1 lsl (7 - l)),`LEN:num`;
      b,`B:num`] headtm))) in
  mk,mk;;

let LSAFE_TEST_TAC k =
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O3_EXEC (1--1) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O3_EXEC (2--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (fun (asl,w) ->
     match find_terms is_cond w with
       [] -> ALL_TAC (asl,w)
     | tms ->
         let c = rand(rator(rator(hd(sort (fun a b -> free_in b a) tms)))) in
         if c = subst [k,`K:num`] `i + 1 < K` then ALL_TAC (asl,w) else
         (SUBGOAL_THEN (mk_eq(c,subst [k,`K:num`] `~(i + 1 < K)`))
          SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) (asl,w)) THEN
  REPEAT(CONJ_TAC THENL
   [REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    (ASM_ARITH_TAC ORELSE (AP_TERM_TAC THEN ASM_ARITH_TAC));
    ALL_TAC]) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The whole safety proof for layer l ***)

let NTT_LAYER_SAFE_TAC l =
  let k = mk_small_numeral(1 lsl l - 1) in
  let blk0_tac =
    ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_poly_ntt_loop2_test1`
     (lsafe_blockend_tm l `1`) THEN
    CONJ_TAC THENL
     [ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_poly_ntt_loop2`
       (lsafe_blockhead_tm l `0`) THEN
      CONJ_TAC THENL
       [NTT_SAFE_SIM_TAC ALL_TAC 8;
        EVENTS_LEMMA_TAC (ntt_block_events_inst l `0`)];
      NTT_SAFE_SIM_TAC ALL_TAC 2] in
  CONCRETIZE_F_EVENTS_TAC (lsafe_template l) THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  NTT_SAFE_FRAME_TAC THEN
  if l = 0 then blk0_tac else
  ENSURES_EVENTS_WHILE_UP2_TAC k `pc + mlkem_poly_ntt_loop2_next1`
   `pc + mlkem_poly_ntt_loop2_exit`
   (mk_abs(`i:num`,lsafe_blockend_tm l `i + 1`)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    REWRITE_TAC[ENUMERATEL; APPEND] THEN CONV_TAC NUM_REDUCE_CONV THEN
    blk0_tac;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_poly_ntt_loop2_test1`
      (lsafe_blockend_tm l `i + 1 + 1`) THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
      ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_poly_ntt_loop2`
        (lsafe_blockhead_tm l `i + 1`) THEN
      CONJ_TAC THENL
       [NTT_SAFE_SIM_TAC
         (let n = rhs(concl(NUM_REDUCE_CONV
                   (subst [mk_small_numeral l,`L:num`] `2 EXP L + i + 1`))) in
          MP_TAC(SPEC n VAL_WORD_ZX_UXTW) THEN
          ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC]) 2;
        EVENTS_LEMMA_TAC (ntt_block_events_inst l `i + 1`)];
      LSAFE_TEST_TAC k];
    NTT_SAFE_SIM_TAC ALL_TAC 0];;

let NTT_GCC12_O3_LAYER_EVENTS = assuming_proofs (fun () ->
  map (fun l ->
        new_specification ["ntt_gcc12_O3_layer_events_" ^ string_of_int l]
                          (prove(lsafe_goal l,NTT_LAYER_SAFE_TAC l)))
      (0--6));;

(*** The whole code, which has the same signature as mlkem_reduce, with the
 *** table of zetas and the vector of 3329^-1 mod 2^16 as read-only objects.
 *** The stack pointer after saving X19 to X21 and X30 is the parameter sp.
 ***)

let ntt_top_template =
  let lay l = list_mk_comb
   (mk_const("ntt_gcc12_O3_layer_events_" ^ string_of_int l,[]),
    [`a:int64`; `pc + rodata_mlk_zetas`; `pc:num`])
  and fev n =
    list_mk_comb
     (mk_var(n,`:int64->num->int64->int64->(uarch_event)list`),
      [`a:int64`;`pc:num`;`sp:int64`;`returnaddress:int64`]) in
  let app x y = list_mk_icomb "APPEND" [x;y] in
  let rec chain l acc =
    let acc' = app (lay l) acc in
    if l = 6 then acc' else
    chain (l + 1) (app (fev ("f_ev_back" ^ string_of_int l)) acc') in
  let body = app (fev "f_ev_fin") (chain 0 (fev "f_ev_init")) in
  list_mk_abs([`a:int64`;`pc:num`;`sp:int64`;`returnaddress:int64`],body);;

let ntt_safe_layerhead_tm,ntt_safe_layerend_tm =
  let stk =
   `read SP s = stackpointer /\
    read(memory :> bytes64 stackpointer) s = x19_init /\
    read(memory :> bytes64(word_add stackpointer (word 8))) s = x20_init /\
    read(memory :> bytes64(word_add stackpointer (word 16))) s = x21_init /\
    read(memory :> bytes64(word_add stackpointer (word 24))) s =
    returnaddress` in
  let headtm =
   `\s. read X11 s = word L /\ read X4 s = a /\
        read X17 s = word_add a (word 2) /\
        read X14 s = word(pc + rodata_mlk_zetas) /\
        read X18 s = word 1 /\ read X30 s = word 256 /\ STK`
  and endtm =
   `\s. read X16 s = word(L + 1) /\ read X4 s = a /\
        read X17 s = word_add a (word 2) /\
        read X14 s = word(pc + rodata_mlk_zetas) /\
        read X18 s = word 1 /\ read X30 s = word 256 /\ STK` in
  let mk tm l =
    let tm' = subst [mk_small_numeral l,`L:num`]
                (mk_abs(`s:armstate`,
                   subst [stk,`STK:bool`] (body tm))) in
    rhs(concl(NUM_REDUCE_CONV tm')) in
  (fun l -> mk headtm l),(fun l -> mk endtm l);;

let ntt_layer_events_inst l ev =
  SPECL [ev; `a:int64`; `pc + rodata_mlk_zetas`; `pc:num`;
         `stackpointer:int64`; `x19_init:int64`; `x20_init:int64`;
         `x21_init:int64`; `returnaddress:int64`]
        (el l NTT_GCC12_O3_LAYER_EVENTS);;

(*** The events of a layer are in bounds for the regions of the whole code ***)

let MEMACCESS_WIDEN_TAC =
  FIRST_X_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Comb(Const("memaccess_inbounds",_),e),rr),wr) ->
        (fun (asl,w) ->
          match w with
            Comb(Comb(Comb(Const("memaccess_inbounds",_),e'),rr'),wr')
            when e' = e ->
              (MP_TAC(ISPECL [e;rr;rr';wr;wr'] MEMACCESS_INBOUNDS_MEM) THEN
               REWRITE_TAC[ALL; MEM] THEN DISCH_THEN MATCH_MP_TAC THEN
               ACCEPT_TAC th) (asl,w)
          | _ -> failwith "MEMACCESS_WIDEN_TAC")
    | _ -> failwith "MEMACCESS_WIDEN_TAC");;

let NTT_SAFE_TOP_TAC =
  CONCRETIZE_F_EVENTS_TAC ntt_top_template THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL; ALLPAIRS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV NORMALIZE_ALIGNED_WORD_CONV)) THEN
  SUBGOAL_THEN `nonoverlapping (a:int64,512)
                  (word(pc + rodata_mlk_zetas),256)` ASSUME_TAC THENL
   [REWRITE_TAC[WORD_ADD] THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN

  (*** Restoring X19 to X21 and X30 and returning after the last layer ***)

  ENSURES_EVENTS_SEQUENCE_TAC
   `pc + mlkem_poly_ntt_loop2_exit` (ntt_safe_layerend_tm 6) THEN
  CONJ_TAC THENL [ALL_TAC; NTT_SAFE_SIM_TAC ALL_TAC 5] THEN

  (*** The layers, with the code between them ***)

  MAP_EVERY (fun l ->
    ENSURES_EVENTS_SEQUENCE_TAC
     `pc + mlkem_poly_ntt_loop1` (ntt_safe_layerhead_tm l) THEN
    CONJ_TAC THENL
     [ALL_TAC;
      EVENTS_LEMMA_TAC (ntt_layer_events_inst l) THEN MEMACCESS_WIDEN_TAC] THEN
    if l = 0 then ALL_TAC else
    ENSURES_EVENTS_SEQUENCE_TAC
     `pc + mlkem_poly_ntt_loop2_exit` (ntt_safe_layerend_tm (l - 1)) THEN
    CONJ_TAC THENL [ALL_TAC; NTT_SAFE_SIM_TAC ALL_TAC 6]) (rev(0--6)) THEN

  (*** The setup of the constants, which also saves X19 to X21 and X30 ***)

  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O3_EXEC (1--3) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O3_EXEC (4--5) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O3_EXEC (6--7) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O3_EXEC (8--18) THEN
  REG_REWRITE_TAC `X14` [GSYM WORD_ADD] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word(pc + rodata_mlk_zetas):int64`,`256`;
                       `word(pc + mlkem_poly_ntt_consts):int64`,
                       `mlkem_poly_ntt_consts_size:num`]
    ~keep_maychanges:true
    (assoc "mlkem_reduce" subroutine_signatures)
    MLKEM_NATIVE_POLY_NTT_GCC12_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_NTT_GCC12_O3_EXEC;;

let MLKEM_NATIVE_POLY_NTT_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e a pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       nonoverlapping (a,512) (word_sub stackpointer (word 32),32) /\
       ALLPAIRS nonoverlapping
        [a,512; word_sub stackpointer (word 32),32]
        [word pc,libmlkem_size]
       ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  mlkem_native_libmlkem_gcc12_O3_mc /\
                read PC s = word (pc + mlkem_poly_ntt) /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [a] s /\
                read events s = e)
           (\s. read PC s = returnaddress /\
                exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_events a pc (word_sub stackpointer (word 32))
                                returnaddress /\
                  memaccess_inbounds e2
                   [a,512; word_sub stackpointer (word 32),32;
                    word (pc + rodata_mlk_zetas),256;
                    word (pc + mlkem_poly_ntt_consts),
                    mlkem_poly_ntt_consts_size]
                   [a,512; word_sub stackpointer (word 32),32])
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
            MAYCHANGE [memory :> bytes(a,512);
                       memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLKEM_NATIVE_POLY_NTT_GCC12_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_NTT_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
