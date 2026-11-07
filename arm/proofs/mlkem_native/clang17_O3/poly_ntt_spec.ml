(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Forward number-theoretic transform from ML-KEM. This is the code for      *)
(* mlkem_poly_ntt from mlkem-native's portable C implementation compiled by  *)
(* clang 17 with -O3 (see mlkem_native/README.md), verified in the whole     *)
(* image (see libmlkem.ml) with the specification of the gcc 12 code.        *)
(*                                                                           *)
(* clang has unrolled the layers and the blocks and vectorized the           *)
(* butterflies. Layers 1 to 4 are straight-line code that keeps the          *)
(* coefficients in vector registers and spills some of them to the stack,    *)
(* layers 5 and 6 are loops, of 16 iterations of 16 coefficients and 32      *)
(* iterations of 8, and layer 7 is straight-line code again, which loads its *)
(* zetas as vectors of constants from mlkem_poly_ntt_consts. Where the zeta  *)
(* z of a Montgomery multiplication is a constant, clang computes the        *)
(* quotient with z * 3329^-1 mod 2^16, and where it is loaded from the table *)
(* of zetas, with 3329^-1 after the product.                                 *)
(*                                                                           *)
(* The code saves D8-D15 and X29 and uses 352 more bytes of stack, so the    *)
(* specification has a stack frame of 432 bytes, where the gcc 12 -O2 code   *)
(* has none and the -O3 code 32 bytes. As for gcc 12 -O3, the theorem of     *)
(* constant time and memory safety lists mlkem_poly_ntt_consts as read-only  *)
(* data besides the zetas. The proof splits the code at the loops. The       *)
(* straight-line parts are simulated with the coefficients as 128-bit words, *)
(* and the results are folded into the C model layer by layer with the       *)
(* equations of NTT_LAYER_EQUATION.                                          *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/interleave.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;
needs "common/int_linear.ml";;

let MLKEM_NATIVE_POLY_NTT_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_poly_ntt"];;

(* ------------------------------------------------------------------------- *)
(* The computation done by the C code, with its 16-bit and 32-bit integer    *)
(* arithmetic, as for gcc 12. The NTT is done in 7 layers, layer l+1         *)
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
(* The lanes of the vector code. clang computes the Montgomery quotient of t *)
(* = x * z as the high half of t * (z * 3329^-1 mod 2^16) * 2^16, with the   *)
(* constant computed at compile time where z is known, and multiplies by     *)
(* 3329^-1 * 2^16 where it is not, as in the code for the basemul.           *)
(* ------------------------------------------------------------------------- *)

let WORD_ISHR_16_SUBWORD_STMT =
  `!w:int32. word_ishr w 16 = word_sx(word_subword w (16,16):int16)`;;

let WORD_ISHR_16_SUBWORD = assume_spec WORD_ISHR_16_SUBWORD_STMT;;

let MULCACHE_QUOT_STMT =
  `!y:int32 z r.
     (z * 62209) MOD 65536 = r
     ==> word_ishr (word_mul y (word (65536 * r))) 16 =
         word_sx (word_mul (word_subword (word_mul y (word z)) (0,16))
                           (word 62209):int16)`;;

let MULCACHE_QUOT = assume_spec MULCACHE_QUOT_STMT;;

let MULCACHE_LANE_STMT =
  `!x:int16 z q.
     65536 * (z * 62209) MOD 65536 = q
     ==> word_subword
          (word_add
            (word_mul
              (word_ishr (word_mul (word_shl (word_sx x:int32) 0) (word q)) 16)
              (word 4294963967))
            (word_mul (word_sx x) (word z))) (16,16):int16 =
         montred_scalar (word_mul (word_sx x) (word z))`;;

let MULCACHE_LANE = assume_spec MULCACHE_LANE_STMT;;

let MULCACHE_LANE_CONV =
  let pat = lhand(rand(snd(strip_forall(concl MULCACHE_LANE)))) in
  fun tm ->
    let ins = term_match [] pat tm in
    let th = INSTANTIATE ins (SPEC_ALL MULCACHE_LANE) in
    MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))));;

let BASEMUL_LANE_STMT =
  `!t:int32.
     word_subword
      (word_add (word_mul (word_ishr (word_mul t (word 4076929024)) 16)
                          (word 4294963967)) t) (16,16):int16 =
     montred_scalar t`;;

let BASEMUL_LANE = assume_spec BASEMUL_LANE_STMT;;

let BASEMUL_LANE_CONV =
  let pat = lhand(snd(strip_forall(concl BASEMUL_LANE))) in
  fun tm -> INSTANTIATE (term_match [] pat tm) (SPEC_ALL BASEMUL_LANE);;

(* ------------------------------------------------------------------------- *)
(* The simulation, and the lemmas for the loops for layers 5 and 6.          *)
(* ------------------------------------------------------------------------- *)

let WORD_SHL_WORD_NUM_STMT =
  `!n k. word_shl (word n:int64) k = word(2 EXP k * n)`;;

let WORD_SHL_WORD_NUM = assume_spec WORD_SHL_WORD_NUM_STMT;;

let NTT_SHL_RULES = map (fun t -> prove(t, REWRITE_TAC[WORD_SHL_WORD_NUM] THEN
     AP_TERM_TAC THEN ARITH_TAC))
  [`word_shl (word (2 * i):int64) 4 = word(32 * i)`;
   `word_shl (word (2 * i):int64) 3 = word(16 * i)`];;

let CHUNK16_INPUT_SPLIT_STMT =
  `!P i. i < 16
         ==> ((!j. 16 * i <= j /\ j < 256 ==> P j) <=>
              (!j. 16 * (i + 1) <= j /\ j < 256 ==> P j) /\
              (!k. k < 16 ==> P(16 * i + k)))`;;

let CHUNK16_INPUT_SPLIT = assume_spec CHUNK16_INPUT_SPLIT_STMT;;

let CHUNK16_OUTPUT_SPLIT_STMT =
  `!P i. (!j. j < 16 * (i + 1) ==> P j) <=>
         (!j. j < 16 * i ==> P j) /\ (!k. k < 16 ==> P(16 * i + k))`;;

let CHUNK16_OUTPUT_SPLIT = assume_spec CHUNK16_OUTPUT_SPLIT_STMT;;

let NTT_STEP_TAC n =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_CLANG17_O3_EXEC [n] THEN
  MLKEM_NATIVE_ADRP_TAC THEN MLKEM_NATIVE_INTERLEAVE_TAC THEN
  SIMD_SIMPLIFY_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE NTT_SHL_RULES) THEN
  RULE_ASSUM_TAC(fun th ->
    if free_in `word_ishr:int32->num->int32` (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV(MULCACHE_LANE_CONV ORELSEC
                                   BASEMUL_LANE_CONV)) th else th);;

let NTT_LAYER_LO_STMT =
  `!l x b k.
     l < 7 /\ b < 2 EXP l /\ k < 2 EXP (7 - l)
     ==> ntt_layers_c (SUC l) x (2 * 2 EXP (7 - l) * b + k) =
         word_add (ntt_layers_c l x (2 * 2 EXP (7 - l) * b + k))
                  (ntt_fqmul_c (iword(EL (2 EXP l + b) mlk_zetas))
                     (ntt_layers_c l x ((2 * 2 EXP (7 - l) * b + k) +
                                        2 EXP (7 - l))))`;;

let NTT_LAYER_LO = assume_spec NTT_LAYER_LO_STMT;;

let NTT_LAYER_HI_STMT =
  `!l x b k.
     l < 7 /\ b < 2 EXP l /\ k < 2 EXP (7 - l)
     ==> ntt_layers_c (SUC l) x (2 * 2 EXP (7 - l) * b + 2 EXP (7 - l) + k) =
         word_sub (ntt_layers_c l x (2 * 2 EXP (7 - l) * b + k))
                  (ntt_fqmul_c (iword(EL (2 EXP l + b) mlk_zetas))
                     (ntt_layers_c l x (2 * 2 EXP (7 - l) * b +
                                        2 EXP (7 - l) + k)))`;;

let NTT_LAYER_HI = assume_spec NTT_LAYER_HI_STMT;;

let NTT_NORM_RULE =
  CONV_RULE(NUM_REDUCE_CONV THENC REWRITE_CONV[MULT_ASSOC] THENC
                              NUM_REDUCE_CONV);;
let NTT_L5_LO =
  (NTT_NORM_RULE o REWRITE_RULE[ntt_fqmul_c] o SPEC `4`) NTT_LAYER_LO;;
let NTT_L5_HI =
  (NTT_NORM_RULE o REWRITE_RULE[ntt_fqmul_c] o SPEC `4`) NTT_LAYER_HI;;
let NTT_L6_LO =
  (NTT_NORM_RULE o REWRITE_RULE[ntt_fqmul_c] o SPEC `5`) NTT_LAYER_LO;;
let NTT_L6_HI =
  (NTT_NORM_RULE o REWRITE_RULE[ntt_fqmul_c] o SPEC `5`) NTT_LAYER_HI;;

let NTT_L5_FLAG_STMT =
  `!i. i < 16
       ==> (~(val (word_add (word (2 * i))
                            (word 18446744073709551586):int64) = 0) <=>
            i + 1 < 16)`;;

let NTT_L5_FLAG = assume_spec NTT_L5_FLAG_STMT;;

let NTT_L5_OUT_TAC =
  REWRITE_TAC[WORD_ZX_ZX_32_64; WORD_SHL_ZERO] THEN
  W(fun (asl,w) ->
    let r = rand w in
    let idx = rand r in
    let n = dest_small_numeral(rand idx) in
    if n < 8 then
      MP_TAC(SPECL [`x:num->int16`; `i:num`; mk_small_numeral n] NTT_L5_LO)
    else
      (SUBST1_TAC(ARITH_RULE(mk_eq(idx, subst [mk_small_numeral(n-8),`k:num`]
                                       `16 * i + 8 + k`))) THEN
       MP_TAC(SPECL [`x:num->int16`; `i:num`; mk_small_numeral (n-8)]
                    NTT_L5_HI))) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `i < 16` THEN ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_MUL_SYM];;

let NTT_L5_ADDRS =
  map (fun k ->
    let t = if k < 8 then
      subst [mk_small_numeral k,`k:num`; mk_small_numeral(2*k),`c:num`]
       `word_add a (word(2 * (16 * i + k))):int64 =
        word_add (word_add a (word(32 * i))) (word c)`
    else
      subst [mk_small_numeral k,`k:num`; mk_small_numeral(2*k-16),`c:num`]
       `word_add a (word(2 * (16 * i + k))):int64 =
        word_add (word_add a (word(32 * i + 16))) (word c)` in
    REWRITE_RULE[WORD_ADD_0] (WORD_RULE t)) (0--15);;


let NTT_L5_ADDRS_IN =
  map (fun k ->
    REWRITE_RULE[WORD_ADD_0] (WORD_RULE
     (subst [mk_small_numeral k,`k:num`; mk_small_numeral(2*k),`c:num`]
       `word_add a (word(2 * (16 * i + k))):int64 =
        word_add (word_add a (word(32 * i))) (word c)`))) (0--15);;

let NTT_L6_FLAG_STMT =
  `!i. i < 32
       ==> (~(val (word_add (word (2 * i))
                            (word 18446744073709551554):int64) = 0) <=>
            i + 1 < 32)`;;

let NTT_L6_FLAG = assume_spec NTT_L6_FLAG_STMT;;

let NTT_L6_ADDRS_IN =
  map (fun k ->
    REWRITE_RULE[WORD_ADD_0] (WORD_RULE
     (subst [mk_small_numeral k,`k:num`; mk_small_numeral(2*k),`c:num`]
       `word_add a (word(2 * (8 * i + k))):int64 =
        word_add (word_add a (word(16 * i))) (word c)`))) (0--7);;

let NTT_L6_ADDRS =
  map (fun k ->
    let t = if k < 4 then
      subst [mk_small_numeral k,`k:num`; mk_small_numeral(2*k),`c:num`]
       `word_add a (word(2 * (8 * i + k))):int64 =
        word_add (word_add a (word(16 * i))) (word c)`
    else
      subst [mk_small_numeral k,`k:num`; mk_small_numeral(2*k-8),`c:num`]
       `word_add a (word(2 * (8 * i + k))):int64 =
        word_add (word_add a (word(16 * i + 8))) (word c)` in
    REWRITE_RULE[WORD_ADD_0] (WORD_RULE t)) (0--7);;

let NTT_L6_OUT_TAC =
  REWRITE_TAC[WORD_ZX_ZX_32_64; WORD_SHL_ZERO] THEN
  W(fun (asl,w) ->
    let r = rand w in
    let idx = rand r in
    let n = dest_small_numeral(rand idx) in
    if n < 4 then
      MP_TAC(SPECL [`x:num->int16`; `i:num`; mk_small_numeral n] NTT_L6_LO)
    else
      (SUBST1_TAC(ARITH_RULE(mk_eq(idx, subst [mk_small_numeral(n-4),`k:num`]
                                       `8 * i + 4 + k`))) THEN
       MP_TAC(SPECL [`x:num->int16`; `i:num`; mk_small_numeral (n-4)]
                    NTT_L6_HI))) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `i < 32` THEN ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_MUL_SYM];;

(* ------------------------------------------------------------------------- *)
(* The frame kept through the layers: the stack pointer after the prologue,  *)
(* the return address, and the callee-saved D8-D15 and X29 saved on the     *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let ntt_clang17_frame = define
 `ntt_clang17_frame (sp:int64) (r:int64) (d8:int64) (d9:int64) (d10:int64)
                    (d11:int64) (d12:int64) (d13:int64) (d14:int64)
                    (d15:int64) (x29:int64) s <=>
    read SP s = sp /\ read X30 s = r /\
    read(memory :> bytes64(word_add sp (word 352))) s = d15 /\
    read(memory :> bytes64(word_add sp (word 360))) s = d14 /\
    read(memory :> bytes64(word_add sp (word 368))) s = d13 /\
    read(memory :> bytes64(word_add sp (word 376))) s = d12 /\
    read(memory :> bytes64(word_add sp (word 384))) s = d11 /\
    read(memory :> bytes64(word_add sp (word 392))) s = d10 /\
    read(memory :> bytes64(word_add sp (word 400))) s = d9 /\
    read(memory :> bytes64(word_add sp (word 408))) s = d8 /\
    read(memory :> bytes64(word_add sp (word 416))) s = x29`;;

let NTT_FRAME_EXPAND_TAC =
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ntt_clang17_frame] o
    check (fun th -> can (term_match []
      `ntt_clang17_frame sp r d8 d9 d10 d11 d12 d13 d14 d15 x29 s`)
      (concl th)));;

(*** The layer equations for layers 1 to 4 and 7, folded into the lanes ***)

let NTT_EQS l = map (fun i -> SYM(NTT_LAYER_EQUATION l i)) (0--255);;

let NTT_EQ0 = NTT_EQS 0 and NTT_EQ1 = NTT_EQS 1 and NTT_EQ2 = NTT_EQS 2
and NTT_EQ3 = NTT_EQS 3 and NTT_EQ6 = NTT_EQS 6;;

(*** The 256 input coefficients as the 32 128-bit words of the array ***)

let NTT_MERGE_TAC =
  FIRST_ASSUM(MP_TAC o check (fun th ->
      is_forall(concl th) && free_in `a:int64` (concl th))) THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
  MAP_EVERY (fun k ->
      MP_TAC(CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV
                                   NORMALIZE_RELATIVE_ADDRESS_CONV))
       (READ_MEMORY_MERGE_CONV 3
        (subst [mk_small_numeral(16 * k),`n:num`]
           `read(memory :> bytes128 (word_add a (word n))) s0`)))) (0--31) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN REPEAT DISCH_TAC THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`];;

(*** The 256 output coefficients from the 32 128-bit words, folded with the
 *** layer equations eqs
 ***)

let NTT_SPLIT_TAC sn eqs =
  let pat = subst [mk_var(sn,`:armstate`),`s:armstate`]
              `read (memory :> bytes128 b) s = y` in
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
     (fun th -> rev_itlist (fun e th -> REWRITE_RULE e th) eqs th) o
     CONV_RULE(SIMD_SIMPLIFY_CONV []) o
     CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
     check (fun th -> can (term_match [] pat) (concl th) &&
                      free_in `a:int64` (concl th)))) THEN
  RULE_ASSUM_TAC(fun th ->
      if free_in `bytes16` (concl th) && not(is_forall(concl th))
      then CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV
                                 NORMALIZE_RELATIVE_ADDRESS_CONV)) th
      else th);;

(*** The callee-saved D8-D15 as the low halves of ghost values of Q8-Q15,
 *** so that the simulation keeps what the prologue saves of them
 ***)

let NTT_DREG_GHOST_TAC =
  REWRITE_TAC[DREG_EXPAND_CLAUSES; READ_ZEROTOP_64] THEN
  MAP_EVERY (fun n ->
    GHOST_INTRO_TAC (mk_var("q" ^ string_of_int n,`:int128`))
     (mk_comb(`read:((armstate,int128)component)->armstate->int128`,
              mk_const("Q" ^ string_of_int n,[])))) (8--15);;

let WORD_SUBWORD_ZX_128_64_STMT =
  `!q:int128. word_subword q (0,64):int64 = word_zx q`;;

let WORD_SUBWORD_ZX_128_64 = assume_spec WORD_SUBWORD_ZX_128_64_STMT;;

let WORD_ZX_ZX_64_128_STMT =
  `!x:int64. word_zx(word_zx x:int128):int64 = x`;;

let WORD_ZX_ZX_64_128 = assume_spec WORD_ZX_ZX_64_128_STMT;;

(* ------------------------------------------------------------------------- *)
(* Layers 1 to 4, from the entry to the loop for layer 5. The prologue saves *)
(* D8-D15 and X29 on the stack.                                              *)
(* ------------------------------------------------------------------------- *)

let NTT_PARTA_STMT =
  `!a (x:num->int16) pc sp returnaddress d8 d9 d10 d11 d12 d13 d14 d15 x29.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    aligned 16 sp /\
    nonoverlapping (a,512) (sp,432) /\
    ALLPAIRS nonoverlapping [(a,512); (sp,432)] [(word pc,libmlkem_size)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_clang17_O3_mc /\
           read PC s = word (pc + mlkem_poly_ntt) /\
           read SP s = word_add sp (word 432) /\
           read X30 s = returnaddress /\
           read X0 s = a /\
           word_zx(read Q8 s):int64 = d8 /\ word_zx(read Q9 s):int64 = d9 /\
           word_zx(read Q10 s):int64 = d10 /\
           word_zx(read Q11 s):int64 = d11 /\
           word_zx(read Q12 s):int64 = d12 /\
           word_zx(read Q13 s):int64 = d13 /\
           word_zx(read Q14 s):int64 = d14 /\
           word_zx(read Q15 s):int64 = d15 /\ read X29 s = x29 /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    x i))
      (\s. read PC s = word (pc + mlkem_poly_ntt_loop1) /\
           read X0 s = a /\ read X8 s = word 0 /\
           read X9 s = word(pc + rodata_mlk_zetas) /\
           read X10 s = word 4076929024 /\
           read Q17 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
           ntt_clang17_frame sp returnaddress d8 d9 d10 d11 d12 d13 d14 d15
                             x29 s /\
           (!j. j < 256
                ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                    ntt_layers_c 4 x j))
      (MAYCHANGE [PC; SP; X8; X9; X10; X11; X12; X13; X14; X15; X16; X29] ,,
       MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13;
                  Q14; Q15; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23; Q24; Q25;
                  Q26; Q27; Q28; Q29; Q30; Q31] ,,
       MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(a,512); memory :> bytes(sp,432)])`;;

let NTT_PARTA = assume_spec NTT_PARTA_STMT;;

(* ------------------------------------------------------------------------- *)
(* The loops for layers 5 and 6.                                             *)
(* ------------------------------------------------------------------------- *)

let ntt_l5_inv =
 `\i s. read X0 s = a /\ read X8 s = word(2 * i) /\
        read X9 s = word(pc + rodata_mlk_zetas) /\
        read X10 s = word 4076929024 /\
        read Q17 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
        ntt_clang17_frame sp returnaddress d8 d9 d10 d11 d12 d13 d14 d15
                          x29 s /\
        (!j. j < 16 * i
             ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                 ntt_layers_c 5 x j) /\
        (!j. 16 * i <= j /\ j < 256
             ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                 ntt_layers_c 4 x j)`;;

let NTT_LOOP1_STMT =
  `!a (x:num->int16) pc sp returnaddress d8 d9 d10 d11 d12 d13 d14 d15 x29.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    nonoverlapping (a,512) (sp,432) /\
    nonoverlapping (a,512) (word pc,libmlkem_size)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_clang17_O3_mc /\
           read PC s = word (pc + mlkem_poly_ntt_loop1) /\
           read X0 s = a /\ read X8 s = word 0 /\
           read X9 s = word(pc + rodata_mlk_zetas) /\
           read X10 s = word 4076929024 /\
           read Q17 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
           ntt_clang17_frame sp returnaddress d8 d9 d10 d11 d12 d13 d14 d15 x29
                             s /\
           (!j. j < 256
                ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                    ntt_layers_c 4 x j))
      (\s. read PC s = word (pc + mlkem_poly_ntt_loop1_exit) /\
           read X0 s = a /\
           read X9 s = word(pc + rodata_mlk_zetas) /\
           ntt_clang17_frame sp returnaddress d8 d9 d10 d11 d12 d13 d14 d15 x29
                             s /\
           (!j. j < 256
                ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                    ntt_layers_c 5 x j))
      (MAYCHANGE [PC; X8; X11; X12] ,, MAYCHANGE [Q0; Q1; Q2; Q3; Q4] ,,
       MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(a,512)])`;;

let NTT_LOOP1 = assume_spec NTT_LOOP1_STMT;;

let ntt_l6_inv =
 `\i s. read X0 s = a /\ read X8 s = word(2 * i) /\
        read X9 s = word(pc + rodata_mlk_zetas) /\
        read Q0 s = word 0xf3010000f3010000f3010000f3010000 /\
        read Q1 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
        ntt_clang17_frame sp returnaddress d8 d9 d10 d11 d12 d13 d14 d15
                          x29 s /\
        (!j. j < 8 * i
             ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                 ntt_layers_c 6 x j) /\
        (!j. 8 * i <= j /\ j < 256
             ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                 ntt_layers_c 5 x j)`;;

let NTT_LOOP2_STMT =
  `!a (x:num->int16) pc sp returnaddress d8 d9 d10 d11 d12 d13 d14 d15 x29.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    nonoverlapping (a,512) (sp,432) /\
    nonoverlapping (a,512) (word pc,libmlkem_size)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_clang17_O3_mc /\
           read PC s = word (pc + mlkem_poly_ntt_loop1_exit) /\
           read X0 s = a /\
           read X9 s = word(pc + rodata_mlk_zetas) /\
           ntt_clang17_frame sp returnaddress d8 d9 d10 d11 d12 d13 d14 d15 x29
                             s /\
           (!j. j < 256
                ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                    ntt_layers_c 5 x j))
      (\s. read PC s = word (pc + mlkem_poly_ntt_loop2_exit) /\
           read X0 s = a /\
           ntt_clang17_frame sp returnaddress d8 d9 d10 d11 d12 d13 d14 d15 x29
                             s /\
           (!j. j < 256
                ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                    ntt_layers_c 6 x j))
      (MAYCHANGE [PC; X8; X10; X11] ,, MAYCHANGE [Q0; Q1; Q2; Q3; Q4] ,,
       MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(a,512)])`;;

let NTT_LOOP2 = assume_spec NTT_LOOP2_STMT;;

(* ------------------------------------------------------------------------- *)
(* Layer 7, with the vectors of constants from the read-only data, and the   *)
(* epilogue, which restores D8-D15 and X29.                                  *)
(* ------------------------------------------------------------------------- *)

let NTT_CONSTANTS =
  map (fun k ->
    MLKEM_NATIVE_IMAGE_CONST_RULE
     (layout("mlkem_poly_ntt_const" ^ string_of_int k))
     (if k <= 16 then 128 else 64)) (1--32);;

let NTT_PARTD_STMT =
  `!a (x:num->int16) pc sp returnaddress d8 d9 d10 d11 d12 d13 d14 d15 x29.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    aligned 16 sp /\
    nonoverlapping (a,512) (sp,432) /\
    ALLPAIRS nonoverlapping [(a,512); (sp,432)] [(word pc,libmlkem_size)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_clang17_O3_mc /\
           read PC s = word (pc + mlkem_poly_ntt_loop2_exit) /\
           read X0 s = a /\
           ntt_clang17_frame sp returnaddress d8 d9 d10 d11 d12 d13 d14 d15
                             x29 s /\
           (!j. j < 256
                ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                    ntt_layers_c 6 x j))
      (\s. read PC s = returnaddress /\
           read SP s = word_add sp (word 432) /\
           read X30 s = returnaddress /\
           word_zx(read Q8 s):int64 = d8 /\ word_zx(read Q9 s):int64 = d9 /\
           word_zx(read Q10 s):int64 = d10 /\
           word_zx(read Q11 s):int64 = d11 /\
           word_zx(read Q12 s):int64 = d12 /\
           word_zx(read Q13 s):int64 = d13 /\
           word_zx(read Q14 s):int64 = d14 /\
           word_zx(read Q15 s):int64 = d15 /\ read X29 s = x29 /\
           (!j. j < 256
                ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                    ntt_layers_c 7 x j))
      (MAYCHANGE [PC; SP; X8; X9; X10; X11; X12; X13; X14; X15; X16; X29] ,,
       MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13;
                  Q14; Q15; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23; Q24; Q25;
                  Q26; Q27; Q28; Q29; Q30; Q31] ,,
       MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(a,512); memory :> bytes(sp,352)])`;;

let NTT_PARTD = assume_spec NTT_PARTD_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_NTT_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a (x:num->int16) pc stackpointer returnaddress.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    aligned 16 stackpointer /\
    nonoverlapping (a,512) (word_sub stackpointer (word 432),432) /\
    ALLPAIRS nonoverlapping
     [(a,512); (word_sub stackpointer (word 432),432)]
     [(word pc,libmlkem_size)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_clang17_O3_mc /\
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
                  memory :> bytes(word_sub stackpointer (word 432),432)])`;;

let MLKEM_NATIVE_POLY_NTT_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_NTT_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let NTT_SAFE_STEP_TAC n =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_CLANG17_O3_EXEC [n] THEN
  MLKEM_NATIVE_ADRP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE NTT_SHL_RULES);;

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word(pc + rodata_mlk_zetas):int64`,`256`;
                       `word(pc + mlkem_poly_ntt_consts):int64`,
                       `mlkem_poly_ntt_consts_size:num`]
    ~keep_maychanges:true
    (assoc "mlkem_reduce" subroutine_signatures)
    MLKEM_NATIVE_POLY_NTT_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_NTT_CLANG17_O3_EXEC;;

let MLKEM_NATIVE_POLY_NTT_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e a pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       nonoverlapping (a,512) (word_sub stackpointer (word 432),432) /\
       ALLPAIRS nonoverlapping
        [a,512; word_sub stackpointer (word 432),432]
        [word pc,libmlkem_size]
       ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  mlkem_native_libmlkem_clang17_O3_mc /\
                read PC s = word (pc + mlkem_poly_ntt) /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [a] s /\
                read events s = e)
           (\s. read PC s = returnaddress /\
                exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_events a pc (word_sub stackpointer (word 432))
                                returnaddress /\
                  memaccess_inbounds e2
                   [a,512; word_sub stackpointer (word 432),432;
                    word (pc + rodata_mlk_zetas),256;
                    word (pc + mlkem_poly_ntt_consts),
                    mlkem_poly_ntt_consts_size]
                   [a,512; word_sub stackpointer (word 432),432])
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
            MAYCHANGE [memory :> bytes(a,512);
                       memory :> bytes(word_sub stackpointer (word 432),
                                       432)])`;;

let MLKEM_NATIVE_POLY_NTT_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_NTT_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
