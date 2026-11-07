(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Inverse number-theoretic transform from ML-KEM. This is the code for      *)
(* mlkem_poly_invntt_tomont from mlkem-native's portable C implementation    *)
(* compiled by clang 17 with -O3 (see mlkem_native/README.md), verified in   *)
(* the whole image (see libmlkem.ml) with the specification of the gcc 12    *)
(* code.                                                                     *)
(*                                                                           *)
(* clang has unrolled the layers and the blocks and vectorized the           *)
(* butterflies. The scaling of the coefficients and layers 7, 6 and 5 are    *)
(* loops over 16, 32, 32 and 16 coefficients at a time, layers 4, 3 and 2    *)
(* are straight-line code that keeps the coefficients in vector registers    *)
(* and spills some of them to the stack, and layer 1 is a loop over 8 + 8    *)
(* coefficients 128 apart. The loop for layer 6 loads the coefficients one   *)
(* by one into vector lanes and puts the results in order with TBL and the   *)
(* vectors of constants mlkem_poly_invntt_tomont_const1 to const8. Where the *)
(* zeta z of a Montgomery multiplication is a constant, clang computes the   *)
(* quotient with z * 3329^-1 mod 2^16, and where it is loaded from the table *)
(* of zetas, with 3329^-1 after the product.                                 *)
(*                                                                           *)
(* The code saves D8-D15 and X29 after the scaling loop and uses 608 more    *)
(* bytes of stack, so the specification has a stack frame of 688 bytes,      *)
(* where the gcc 12 -O3 code has 32 bytes. As for gcc 12 -O3, the theorem of *)
(* constant time and memory safety lists mlkem_poly_invntt_tomont_consts as  *)
(* read-only data besides the zetas. The proof splits the code at the loops; *)
(* the straight-line part is simulated with the coefficients as 128-bit      *)
(* words, and the results are folded into the C model layer by layer with    *)
(* the equations of INVNTT_LAYER_EQUATION.                                   *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/interleave.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;
needs "common/int_linear.ml";;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_poly_invntt_tomont"];;

(* ------------------------------------------------------------------------- *)
(* The computation done by the C code, with its 16-bit and 32-bit integer    *)
(* arithmetic, as for gcc 12. The coefficients are first scaled by a         *)
(* Montgomery multiplication by 1441 = 2^25 mod 3329. Then the inverse NTT   *)
(* is done in 7 layers, for l = 7 down to 1, layer l consisting of 2^(l-1)   *)
(* blocks of 2^(9-l) consecutive coefficients. A block uses one zeta to do   *)
(* butterflies on pairs of coefficients 2^(8-l) apart, independently, with a *)
(* Barrett reduction of the sums.                                            *)
(* ------------------------------------------------------------------------- *)

let invntt_scale_c = define
 `invntt_scale_c (x:num->int16) i =
    montred_neon(word_mul (word_sx(x i)) (word 1441))`;;

let invntt_fqmul_c = define
 `invntt_fqmul_c (z:int16) (y:int16) =
    montred_scalar(word_mul (word_sx y) (word_sx z))`;;

let invntt_block_c = define
 `invntt_block_c (z:int16) start len (m:num->int16) i =
    if start <= i /\ i < start + len
    then barred(word_add (m i) (m(i + len)))
    else if start + len <= i /\ i < start + 2 * len
    then invntt_fqmul_c z (word_sub (m i) (m(i - len)))
    else m i`;;

let invntt_blocks_c = define
 `invntt_blocks_c l 0 (r:num->int16) = r /\
  invntt_blocks_c l (SUC b) r =
    invntt_block_c (iword(EL (2 EXP l - 1 - b) mlk_zetas))
                   (2 * 2 EXP (8 - l) * b) (2 EXP (8 - l))
                   (invntt_blocks_c l b r)`;;

let invntt_layers_c = define
 `invntt_layers_c 0 (x:num->int16) = x /\
  invntt_layers_c (SUC n) x =
    invntt_blocks_c (7 - n) (2 EXP (6 - n)) (invntt_layers_c n x)`;;

let INVNTT_BLOCKS_C_CLOSED_STMT =
  `!l b r i.
     invntt_blocks_c l b r i =
     if i < 2 * 2 EXP (8 - l) * b
     then let z = iword(EL (2 EXP l - 1 - i DIV (2 * 2 EXP (8 - l)))
                           mlk_zetas) in
          if i MOD (2 * 2 EXP (8 - l)) < 2 EXP (8 - l)
          then barred(word_add (r i) (r(i + 2 EXP (8 - l))))
          else invntt_fqmul_c z (word_sub (r i) (r(i - 2 EXP (8 - l))))
     else r i`;;

let INVNTT_BLOCKS_C_CLOSED = assume_spec INVNTT_BLOCKS_C_CLOSED_STMT;;

let INVNTT_LAYERS_C_STEP_STMT =
  `!n x i.
     n < 7 /\ i < 256
     ==> invntt_layers_c (SUC n) x i =
         let z = iword(EL (2 EXP (7 - n) - 1 -
                           i DIV (2 * 2 EXP (8 - (7 - n)))) mlk_zetas) in
         if i MOD (2 * 2 EXP (8 - (7 - n))) < 2 EXP (8 - (7 - n))
         then barred(word_add (invntt_layers_c n x i)
                        (invntt_layers_c n x (i + 2 EXP (8 - (7 - n)))))
         else invntt_fqmul_c z
                (word_sub (invntt_layers_c n x i)
                          (invntt_layers_c n x (i - 2 EXP (8 - (7 - n)))))`;;

let INVNTT_LAYERS_C_STEP = assume_spec INVNTT_LAYERS_C_STEP_STMT;;

let MLK_ZETAS_ELS =
  map (fun k -> (REWRITE_CONV[mlk_zetas] THENC EL_CONV)
                 (mk_comb(mk_comb(`EL:num->int list->int`,mk_small_numeral k),
                          `mlk_zetas`))) (0--127);;

(*** The equation for coefficient i after layer n + 1, starting from the
 *** scaled coefficients
 ***)

let INVNTT_LAYER_EQUATION =
  let conv =
    NUM_REDUCE_CONV THENC TOP_DEPTH_CONV let_CONV THENC
    REWRITE_CONV(CONJUNCT1 invntt_layers_c :: invntt_scale_c ::
                 MONTRED_NEON_SCALAR :: MLK_ZETAS_ELS) THENC
    ONCE_DEPTH_CONV WORD_IWORD_CONV THENC REWRITE_CONV[invntt_fqmul_c] THENC
    DEPTH_CONV WORD_RED_CONV in
  fun n i ->
    let th = SPECL [mk_small_numeral n; `invntt_scale_c x`;
                    mk_small_numeral i] INVNTT_LAYERS_C_STEP in
    let th' = MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))) in
    CONV_RULE(BINOP_CONV conv) th';;

(*** The congruences and bounds for all the layers, in order ***)

let INVNTT_LAYERS_CONGBOUND =
  MLKEM_NATIVE_LOCAL_CONGBOUND_RULE undefined
   (map (fun (n,i) -> SYM(INVNTT_LAYER_EQUATION n i))
        (List.concat (map (fun n -> map (fun i -> (n,i)) (0--255)) (0--6))));;

let INVNTT_FINAL_TAC =
  W(fun (asl,w) ->
    let tm = find_term
      (can (term_match [] `invntt_layers_c 7 (invntt_scale_c x) i`)) w in
    let th = apply INVNTT_LAYERS_CONGBOUND tm in
    if not(fst(dest_const(repeat rator w)) = "int_le") then
      MP_TAC(CONJUNCT1 th) THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_TRANS) THEN
      CONV_TAC(ONCE_DEPTH_CONV INVERSE_NTT_CONV) THEN
      REWRITE_TAC[GSYM INT_REM_EQ; o_THM] THEN CONV_TAC INT_REM_DOWN_CONV THEN
      REWRITE_TAC[INT_REM_EQ] THEN INT_LINEAR_CONG_TAC
    else
      MP_TAC(CONJUNCT2 th) THEN INT_ARITH_TAC);;

let INVNTT_LAYERS_C_CORRECT_STMT =
  `!x i. i < 256
         ==> (ival(invntt_layers_c 7 (invntt_scale_c x) i) ==
              inverse_ntt (ival o x) i) (mod &3329) /\
             abs(ival(invntt_layers_c 7 (invntt_scale_c x) i)) <= &26624`;;

let INVNTT_LAYERS_C_CORRECT = assume_spec INVNTT_LAYERS_C_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* The lanes of the vector code. A Montgomery multiplication by a constant   *)
(* zeta z computes the quotient with z * 3329^-1 mod 2^16 (as in             *)
(* poly_mulcache_compute), and one by a zeta loaded from the table           *)
(* multiplies the product by 3329^-1 (as in basemul). The Barrett reduction  *)
(* of a sum is as for gcc 12 -O3.                                            *)
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

let BARRED_VEC_LANE_STMT =
  `!t:int16.
     word_add t
      (word_mul
        (word_subword
          (word_ishr (word_add (word_mul (word_sx t) (word 20159))
                               (word 33554432)) 26:int32) (0,16))
        (word 62207)) =
     barred t`;;

let BARRED_VEC_LANE = assume_spec BARRED_VEC_LANE_STMT;;

(*** TBL selects bytes. These rules put the bytes of the 16-bit lanes
 *** together again, so that SIMD_SIMPLIFY_CONV can take the lanes apart.
 ***)

let INVNTT_TBL_RULES =
  let mk ty k =
    let tm = subst [mk_small_numeral (k + 8),`m:num`;
                    mk_small_numeral k,`k:num`]
      (inst [hd(snd(dest_type ty)),`:N`]
        `word_join (word_subword (y:N word) (m,8):byte)
                   (word_subword (y:N word) (k,8):byte):int16 =
         word_subword y (k,16)`) in
    prove(tm, CONV_TAC WORD_BLAST) in
  [prove(`!x:int16. word_join (word_subword x (8,8):byte)
                              (word_subword x (0,8):byte) = x`,
         CONV_TAC WORD_BLAST)] @
  map (mk `:int128`) (map (fun j -> 16 * j) (0--7)) @
  map (mk `:int64`) (map (fun j -> 16 * j) (0--3)) @
  map (fun p ->
    prove(subst [mk_small_numeral p,`p:num`]
           `!x:int64.
              word_subword (word_subword x (0,64):int128) (p,16):int16 =
              word_subword x (p,16)`,
          CONV_TAC WORD_BLAST)) (map (fun j -> 16 * j) (0--3));;

(* ------------------------------------------------------------------------- *)
(* The state kept through the layers: the registers that the ABI preserves   *)
(* before the prologue, with D8-D15 as the low halves of Q8-Q15, and the     *)
(* stack pointer, return address and saved registers after it.               *)
(* ------------------------------------------------------------------------- *)

let invntt_clang17_entry = define
 `invntt_clang17_entry (sp:int64) (r:int64) (d8:int64) (d9:int64) (d10:int64)
                       (d11:int64) (d12:int64) (d13:int64) (d14:int64)
                       (d15:int64) (x29:int64) s <=>
    read SP s = sp /\ read X30 s = r /\
    word_zx(read Q8 s):int64 = d8 /\ word_zx(read Q9 s):int64 = d9 /\
    word_zx(read Q10 s):int64 = d10 /\ word_zx(read Q11 s):int64 = d11 /\
    word_zx(read Q12 s):int64 = d12 /\ word_zx(read Q13 s):int64 = d13 /\
    word_zx(read Q14 s):int64 = d14 /\ word_zx(read Q15 s):int64 = d15 /\
    read X29 s = x29`;;

let INVNTT_ENTRY_EXPAND_TAC =
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[invntt_clang17_entry] o
    check (fun th -> can (term_match []
      `invntt_clang17_entry sp r d8 d9 d10 d11 d12 d13 d14 d15 x29 s`)
      (concl th)));;

let invntt_clang17_frame = define
 `invntt_clang17_frame (sp:int64) (r:int64) (d8:int64) (d9:int64) (d10:int64)
                       (d11:int64) (d12:int64) (d13:int64) (d14:int64)
                       (d15:int64) (x29:int64) s <=>
    read SP s = sp /\ read X30 s = r /\
    read(memory :> bytes64(word_add sp (word 608))) s = d15 /\
    read(memory :> bytes64(word_add sp (word 616))) s = d14 /\
    read(memory :> bytes64(word_add sp (word 624))) s = d13 /\
    read(memory :> bytes64(word_add sp (word 632))) s = d12 /\
    read(memory :> bytes64(word_add sp (word 640))) s = d11 /\
    read(memory :> bytes64(word_add sp (word 648))) s = d10 /\
    read(memory :> bytes64(word_add sp (word 656))) s = d9 /\
    read(memory :> bytes64(word_add sp (word 664))) s = d8 /\
    read(memory :> bytes64(word_add sp (word 672))) s = x29`;;

let INVNTT_FRAME_EXPAND_TAC =
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[invntt_clang17_frame] o
    check (fun th -> can (term_match []
      `invntt_clang17_frame sp r d8 d9 d10 d11 d12 d13 d14 d15 x29 s`)
      (concl th)));;

(*** The callee-saved D8-D15 as the low halves of ghost values of Q8-Q15,
 *** so that the simulation keeps what the prologue saves of them
 ***)

let INVNTT_DREG_GHOST_TAC =
  REWRITE_TAC[invntt_clang17_entry] THEN
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
(* The simulation, and lemmas for the loops.                                 *)
(* ------------------------------------------------------------------------- *)

let INVNTT_STEP_TAC n =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O3_EXEC [n] THEN
  MLKEM_NATIVE_ADRP_TAC THEN MLKEM_NATIVE_INTERLEAVE_TAC THEN
  SIMD_SIMPLIFY_TAC[] THEN
  RULE_ASSUM_TAC(fun th ->
    if free_in `word_ishr:int32->num->int32` (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV(MULCACHE_LANE_CONV ORELSEC
                                   BASEMUL_LANE_CONV ORELSEC
                                   REWR_CONV BARRED_VEC_LANE)) th
    else if can (find_term (fun t -> type_of t = `:byte`)) (concl th)
    then CONV_RULE(SIMD_SIMPLIFY_CONV[]) (REWRITE_RULE INVNTT_TBL_RULES th)
    else th);;

(*** The flags at the end of a loop body: m * i is the counter before the
 *** iteration, compared with m * n after it
 ***)

let LOOP_FLAG_RULE m n =
  let tw = Num.power_num (Num.num_of_int 2) (Num.num_of_int 64) in
  let c = Num.sub_num tw (Num.num_of_int (m * (n - 1))) in
  let sub = [mk_small_numeral m,`m:num`; mk_small_numeral n,`n:num`;
             mk_numeral c,`c:num`; mk_small_numeral(n-1),`p:num`] in
  prove(vsubst sub
   `!i. i < n
        ==> (~(val (word_add (word (m * i)) (word c):int64) = 0) <=>
             i + 1 < n)`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
   ASM_CASES_TAC (vsubst sub `(i:num) = (p:num)`) THEN ASM_REWRITE_TAC[] THEN
   CONV_TAC NUM_REDUCE_CONV THEN
   ASM_SIMP_TAC[MOD_LT; ARITH_RULE(vsubst sub
    `i < n /\ ~(i = p) ==> m * i + c < 18446744073709551616`)] THEN
   SIMPLE_ARITH_TAC);;

(*** Splitting off the coefficients of one iteration, and their addresses
 ***)

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

let CHUNK_INPUT_SPLIT_RULE n =
  let sub = [mk_small_numeral n,`n:num`; mk_small_numeral (256 / n),`p:num`] in
  prove(vsubst sub
   `!P i. i < p
          ==> ((!j. n * i <= j /\ j < 256 ==> P j) <=>
               (!j. n * (i + 1) <= j /\ j < 256 ==> P j) /\
               (!k. k < n ==> P(n * i + k)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    STRIP_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC (vsubst sub `n * (i + 1) <= j`) THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC (vsubst sub `j - n * i`)) THEN
    ASM_SIMP_TAC[ARITH_RULE(vsubst sub
      `n * i <= j ==> n * i + (j - n * i) = j`)] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let CHUNK_OUTPUT_SPLIT_RULE n =
  let sub = [mk_small_numeral n,`n:num`] in
  prove(vsubst sub
   `!P i. (!j. j < n * (i + 1) ==> P j) <=>
          (!j. j < n * i ==> P j) /\ (!k. k < n ==> P(n * i + k))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    STRIP_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC (vsubst sub `j < n * i`) THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC (vsubst sub `j - n * i`)) THEN
    ASM_SIMP_TAC[ARITH_RULE(vsubst sub
      `~(j < n * i) ==> n * i + (j - n * i) = j`)] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let CHUNK32_INPUT_SPLIT = CHUNK_INPUT_SPLIT_RULE 32;;

let CHUNK32_OUTPUT_SPLIT = CHUNK_OUTPUT_SPLIT_RULE 32;;

let CHUNK_ADDRS_IN n =
  map (fun k ->
    REWRITE_RULE[WORD_ADD_0] (WORD_RULE
     (subst [mk_small_numeral n,`n:num`; mk_small_numeral (2 * n),`w:num`;
             mk_small_numeral k,`k:num`; mk_small_numeral(2*k),`c:num`]
       `word_add a (word(2 * (n * i + k))):int64 =
        word_add (word_add a (word(w * i))) (word c)`))) (0--(n-1));;

let CHUNK_ADDRS_FLAT n =
  map (fun k ->
    let sub = [mk_small_numeral n,`n:num`; mk_small_numeral (2 * n),`w:num`;
               mk_small_numeral k,`k:num`; mk_small_numeral(2*k),`c:num`] in
    let t = if k = 0 then
      `word_add a (word(2 * (n * i + k))):int64 = word_add a (word(w * i))`
    else
      `word_add a (word(2 * (n * i + k))):int64 =
       word_add a (word(w * i + c))` in
    let th = subst sub t in
    prove(th, AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC)) (0--(n-1));;

let CHUNK_ADDRS_OUT n =
  map (fun k ->
    let q = k / 8 and r = k mod 8 in
    let sub = [mk_small_numeral n,`n:num`; mk_small_numeral (2 * n),`w:num`;
               mk_small_numeral k,`k:num`; mk_small_numeral(2*r),`c:num`;
               mk_small_numeral(16*q),`d:num`] in
    let t = if q = 0 then
      `word_add a (word(2 * (n * i + k))):int64 =
       word_add (word_add a (word(w * i))) (word c)`
    else
      `word_add a (word(2 * (n * i + k))):int64 =
       word_add (word_add a (word(w * i + d))) (word c)` in
    REWRITE_RULE[WORD_ADD_0] (WORD_RULE (subst sub t))) (0--(n-1));;

let CHUNK16_ADDRS =
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

let CHUNK16_ADDRS_IN =
  map (fun k ->
    REWRITE_RULE[WORD_ADD_0] (WORD_RULE
     (subst [mk_small_numeral k,`k:num`; mk_small_numeral(2*k),`c:num`]
       `word_add a (word(2 * (16 * i + k))):int64 =
        word_add (word_add a (word(32 * i))) (word c)`))) (0--15);;

(*** The coefficients of iteration i of a loop over the blocks of a layer
 ***)

let INVNTT_NORM_RULE =
  CONV_RULE(NUM_REDUCE_CONV THENC REWRITE_CONV[MULT_ASSOC] THENC
                              NUM_REDUCE_CONV);;

let INVNTT_BLOCK_BOUND_TAC =
  SUBGOAL_THEN `2 * 2 EXP (8 - (7 - n)) * (b + 1) <= 256` MP_TAC THENL
   [TRANS_TAC LE_TRANS `2 * 2 EXP (8 - (7 - n)) * 2 EXP (6 - n)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
      REWRITE_TAC[GSYM MULT_ASSOC; GSYM EXP_ADD] THEN
      ASM_SIMP_TAC[ARITH_RULE `n < 7 ==> 8 - (7 - n) + 6 - n = 7`] THEN
      CONV_TAC NUM_REDUCE_CONV];
    ASM_ARITH_TAC];;

let INVNTT_LAYER_LO_STMT =
  `!n x b k.
     n < 7 /\ b < 2 EXP (6 - n) /\ k < 2 EXP (8 - (7 - n))
     ==> invntt_layers_c (SUC n) x (2 * 2 EXP (8 - (7 - n)) * b + k) =
         barred(word_add
          (invntt_layers_c n x (2 * 2 EXP (8 - (7 - n)) * b + k))
          (invntt_layers_c n x ((2 * 2 EXP (8 - (7 - n)) * b + k) +
                                2 EXP (8 - (7 - n)))))`;;

let INVNTT_LAYER_LO = assume_spec INVNTT_LAYER_LO_STMT;;

let INVNTT_LAYER_HI_STMT =
  `!n x b k.
     n < 7 /\ b < 2 EXP (6 - n) /\ k < 2 EXP (8 - (7 - n))
     ==> invntt_layers_c (SUC n) x
           (2 * 2 EXP (8 - (7 - n)) * b + 2 EXP (8 - (7 - n)) + k) =
         invntt_fqmul_c (iword(EL (2 EXP (7 - n) - 1 - b) mlk_zetas))
          (word_sub
            (invntt_layers_c n x
              (2 * 2 EXP (8 - (7 - n)) * b + 2 EXP (8 - (7 - n)) + k))
            (invntt_layers_c n x (2 * 2 EXP (8 - (7 - n)) * b + k)))`;;

let INVNTT_LAYER_HI = assume_spec INVNTT_LAYER_HI_STMT;;

let INVNTT_LOOP_LO_RULE n c =
  let th = (INVNTT_NORM_RULE o SPEC (mk_small_numeral n))
           INVNTT_LAYER_LO in
  let len = 1 lsl (n + 1) in
  let sub = [mk_small_numeral n,`n:num`; mk_small_numeral c,`c:num`;
             mk_small_numeral (2 * len * c),`w:num`;
             mk_small_numeral (2 * len),`d:num`;
             mk_small_numeral len,`l:num`;
             mk_small_numeral (256 / (2 * len * c)),`p:num`;
             mk_small_numeral (n + 1),`n1:num`] in
  prove(vsubst sub
   `!x i m k.
      i < p /\ m < c /\ k < l
      ==> invntt_layers_c n1 x (w * i + d * m + k) =
          barred(word_add (invntt_layers_c n x (w * i + d * m + k))
                          (invntt_layers_c n x (w * i + d * m + k + l)))`,
   REPEAT STRIP_TAC THEN
   MP_TAC(SPECL [`x:num->int16`; vsubst sub `c * i + m`; `k:num`] th) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[ARITH_RULE(vsubst sub
                `d * (c * i + m) + k = w * i + d * m + k`);
               ARITH_RULE(vsubst sub `(w * i + d * m + k) + l =
                                      w * i + d * m + k + l`)] THEN
   CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let INVNTT_LOOP_HI_RULE n c =
  let th = (INVNTT_NORM_RULE o SPEC (mk_small_numeral n))
           INVNTT_LAYER_HI in
  let len = 1 lsl (n + 1) in
  let sub = [mk_small_numeral n,`n:num`; mk_small_numeral c,`c:num`;
             mk_small_numeral (2 * len * c),`w:num`;
             mk_small_numeral (2 * len),`d:num`;
             mk_small_numeral len,`l:num`;
             mk_small_numeral (256 / (2 * len * c)),`p:num`;
             mk_small_numeral (n + 1),`n1:num`;
             mk_small_numeral ((1 lsl (7 - n)) - 1),`t:num`] in
  prove(vsubst sub
   `!x i m k.
      i < p /\ m < c /\ k < l
      ==> invntt_layers_c n1 x (w * i + d * m + l + k) =
          invntt_fqmul_c (iword(EL (t - (c * i + m)) mlk_zetas))
           (word_sub (invntt_layers_c n x (w * i + d * m + l + k))
                     (invntt_layers_c n x (w * i + d * m + k)))`,
   REPEAT STRIP_TAC THEN
   MP_TAC(SPECL [`x:num->int16`; vsubst sub `c * i + m`; `k:num`] th) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[ARITH_RULE(vsubst sub `d * (c * i + m) + l + k =
                                      w * i + d * m + l + k`);
               ARITH_RULE(vsubst sub
                `d * (c * i + m) + k = w * i + d * m + k`)] THEN
   CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

(*** The zetas, loaded downwards from zeta number c - b * i ***)

let ZETA_ADDR_DOWN_STMT =
  `!z c b i k.
     word_add (word_add (word z) (word(2 * (c - b * i)))) (word(2 * k)):int64 =
     word_add (word z) (word(2 * ((c - b * i) + k)))`;;

let ZETA_ADDR_DOWN = assume_spec ZETA_ADDR_DOWN_STMT;;

let ZETA_PTR_STEP_RULE b c =
  let d = Num.sub_num (Num.power_num (Num.num_of_int 2) (Num.num_of_int 64))
                      (Num.num_of_int (2 * b)) in
  let sub = [mk_small_numeral b,`b:num`; mk_small_numeral c,`c:num`;
             mk_numeral d,`d:num`] in
  prove(vsubst sub
   `!z i. b * (i + 1) <= c
          ==> word_add (word_add (word z) (word(2 * (c - b * i))))
                       (word d):int64 =
              word_add (word z) (word(2 * (c - b * (i + 1))))`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN (vsubst sub `2 * (c - b * i) = 2 * (c - b * (i + 1)) + 2 * b`)
   SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   SPEC_TAC(vsubst sub `2 * (c - b * (i + 1))`,`y:num`) THEN
   GEN_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
   REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
   CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
   REWRITE_TAC[WORD_ADD_0]);;

let ZETA_LANE_ADDRS =
  map (fun m ->
    let th = SPECL [`z:num`; `c:num`; `b:num`; `i:num`; mk_small_numeral m]
                   ZETA_ADDR_DOWN in
    let th' = CONV_RULE(LAND_CONV(RAND_CONV(RAND_CONV NUM_MULT_CONV))) th in
    if m = 0 then REWRITE_RULE[WORD_ADD_0] th' else th') (0--7);;

let INVNTT_ZETAS_TAC reg b c n =
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLK_ZETAS_LOADED o
    MATCH_MP (MLKEM_NATIVE_IMAGE_DATA_RULE mlk_zetas_data
               (layout "rodata_mlk_zetas"))) THEN
  W(fun (asl,w) ->
    let rtm = mk_comb(mk_comb(
      `read:(armstate,int64)component->armstate->int64`,reg),`s0:armstate`) in
    let ptr = find (fun t -> is_eq t && lhs t = rtm) (map (concl o snd) asl) in
    let zth = find (fun th -> is_forall(concl th) &&
                              free_in `mlk_zetas` (concl th)) (map snd asl) in
    let mtm = subst [rand ptr,`t:int64`]
      (if n = 128 then `read(memory :> bytes128 t) s0`
       else if n = 64 then `read(memory :> bytes64 t) s0`
       else `read(memory :> bytes16 t) s0`) in
    let mth = if n = 16 then REFL mtm
              else READ_MEMORY_MERGE_CONV (if n = 128 then 3 else 2) mtm in
    let sub = [mk_small_numeral b,`b:num`; mk_small_numeral c,`c:num`] in
    let lth = map (INST sub) ZETA_LANE_ADDRS in
    let zl = map (fun m ->
        let k = vsubst (sub @ [mk_small_numeral m,`m:num`])
                       `(c - b * i) + m` in
        MP (SPEC k zth) (ARITH_RULE(mk_comb(mk_comb(`(<):num->num->bool`,k),
                                            `128`)))) (0--7) in
    ASSUME_TAC(CONV_RULE(RAND_CONV(REWRITE_CONV lth THENC REWRITE_CONV zl))
                        mth));;

(*** An output of a loop over the blocks of a layer, d coefficients a
 *** block
 ***)

let INVNTT_OUT_TAC p d lo hi =
  REWRITE_TAC[WORD_ZX_ZX_32_64; WORD_SHL_ZERO] THEN
  W(fun (asl,w) ->
    let idx = rand(rand w) in
    let c = dest_small_numeral(rand idx) in
    let m = c / d and r = c mod d in
    let ith = if r < d / 2 then
      SPECL [`invntt_scale_c x`; `i:num`; mk_small_numeral m;
             mk_small_numeral r] lo
    else
      SPECL [`invntt_scale_c x`; `i:num`; mk_small_numeral m;
             mk_small_numeral (r - d / 2)] hi in
    MP_TAC ith THEN
    ANTS_TAC THENL [UNDISCH_TAC p THEN ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[CONJUNCT1 invntt_layers_c; invntt_fqmul_c] THEN
  W(fun (asl,w) ->
    let is_el t = is_comb t && is_comb(rator t) &&
                  rator(rator t) = `EL:num->int list->int` in
    match find_terms is_el w with
      [t1; t2] when not(t1 = t2) ->
        SUBST1_TAC(MP (ARITH_RULE(mk_imp(p,mk_eq(lhand t1,lhand t2))))
                      (ASSUME p))
    | _ -> ALL_TAC) THEN
  REWRITE_TAC[WORD_ADD_SYM];;

let INVNTT_MERGE4_TAC w =
  MP_TAC(READ_MEMORY_MERGE_CONV 3
   (subst [mk_small_numeral w,`w:num`]
     `read(memory :> bytes128(word_add a (word(w * i)))) s0`)) THEN
  MAP_EVERY (fun k ->
    MP_TAC(CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV
                                 NORMALIZE_RELATIVE_ADDRESS_CONV))
     (READ_MEMORY_MERGE_CONV 3
       (subst [mk_small_numeral k,`k:num`; mk_small_numeral w,`w:num`]
         `read(memory :> bytes128(word_add (word_add a (word(w * i)))
                                           (word k))) s0`))))
   (map (fun j -> 16 * j) (1--(w / 16 - 1)));;

let INVNTT_SPLIT_TAC sn =
  let pat = subst [mk_var(sn,`:armstate`),`s:armstate`]
              `read (memory :> bytes128 b) s = y` in
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
     CONV_RULE(SIMD_SIMPLIFY_CONV []) o REWRITE_RULE INVNTT_TBL_RULES o
     CONV_RULE(SIMD_SIMPLIFY_CONV []) o
     CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
     check (fun th -> can (term_match [] pat) (concl th) &&
                      free_in `a:int64` (concl th))));;

(* ------------------------------------------------------------------------- *)
(* The scaling loop at the start.                                            *)
(* ------------------------------------------------------------------------- *)

let INVNTT_SCALE_FLAG = LOOP_FLAG_RULE 32 16;;

let invntt_scale_inv =
 `\i s. read X0 s = a /\ read X8 s = word(32 * i) /\
        read Q0 s = word 0x05a105a105a105a105a105a105a105a1 /\
        read Q1 s = word 0xd8a10000d8a10000d8a10000d8a10000 /\
        read Q2 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
        invntt_clang17_entry sp r d8 d9 d10 d11 d12 d13 d14 d15 x29 s /\
        (!j. j < 16 * i
             ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                 invntt_scale_c x j) /\
        (!j. 16 * i <= j /\ j < 256
             ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                 x j)`;;

let INVNTT_SCALE_STMT =
  `!a (x:num->int16) pc sp r d8 d9 d10 d11 d12 d13 d14 d15 x29.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    nonoverlapping (a,512) (word pc,libmlkem_size)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_clang17_O3_mc /\
           read PC s = word (pc + mlkem_poly_invntt_tomont) /\
           read X0 s = a /\
           invntt_clang17_entry sp r d8 d9 d10 d11 d12 d13 d14 d15 x29 s /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    x i))
      (\s. read PC s = word (pc + mlkem_poly_invntt_tomont_loop1_exit) /\
           read X0 s = a /\
           invntt_clang17_entry sp r d8 d9 d10 d11 d12 d13 d14 d15 x29 s /\
           (!j. j < 256
                ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                    invntt_scale_c x j))
      (MAYCHANGE [PC; X8; X9; X10] ,,
       MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q16; Q17; Q18] ,,
       MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(a,512)])`;;

let INVNTT_SCALE = assume_spec INVNTT_SCALE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Layer 7, a loop over 8 blocks of 4 coefficients at a time, after the      *)
(* prologue.                                                                 *)
(* ------------------------------------------------------------------------- *)

let INVNTT_L7_ADDRS_IN = CHUNK_ADDRS_IN 32;;

let INVNTT_L7_ADDRS = CHUNK_ADDRS_OUT 32;;

let INVNTT_L7_FLAG = LOOP_FLAG_RULE 64 8;;

let INVNTT_L7_PTR = ZETA_PTR_STEP_RULE 8 120;;

let INVNTT_L7_LO = INVNTT_LOOP_LO_RULE 0 8;;

let INVNTT_L7_HI = INVNTT_LOOP_HI_RULE 0 8;;

let invntt_l7_inv =
 `\i s. read X0 s = a /\ read X8 s = word(64 * i) /\
        read X9 s = word_add (word(pc + rodata_mlk_zetas))
                             (word(2 * (120 - 8 * i))) /\
        read Q0 s = word 0x4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf /\
        read Q1 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
        read Q2 s = word 0xf3010000f3010000f3010000f3010000 /\
        read Q3 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
        invntt_clang17_frame sp r d8 d9 d10 d11 d12 d13 d14 d15 x29 s /\
        (!j. j < 32 * i
             ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                 invntt_layers_c 1 (invntt_scale_c x) j) /\
        (!j. 32 * i <= j /\ j < 256
             ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                 invntt_scale_c x j)`;;

let INVNTT_L7_STMT =
  `!a (x:num->int16) pc sp r d8 d9 d10 d11 d12 d13 d14 d15 x29.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    aligned 16 sp /\
    nonoverlapping (a,512) (sp,688) /\
    ALLPAIRS nonoverlapping [(a,512); (sp,688)] [(word pc,libmlkem_size)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_clang17_O3_mc /\
           read PC s = word (pc + mlkem_poly_invntt_tomont_loop1_exit) /\
           read X0 s = a /\
           invntt_clang17_entry (word_add sp (word 688)) r
             d8 d9 d10 d11 d12 d13 d14 d15 x29 s /\
           (!j. j < 256
                ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                    invntt_scale_c x j))
      (\s. read PC s = word (pc + mlkem_poly_invntt_tomont_loop2_exit) /\
           read X0 s = a /\
           invntt_clang17_frame sp r d8 d9 d10 d11 d12 d13 d14 d15 x29 s /\
           (!j. j < 256
                ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                    invntt_layers_c 1 (invntt_scale_c x) j))
      (MAYCHANGE [PC; SP; X8; X9; X10; X11] ,,
       MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q16; Q17; Q18; Q19; Q20;
                  Q21; Q22; Q23; Q24; Q25; Q26] ,,
       MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(a,512); memory :> bytes(sp,688)])`;;

let INVNTT_L7 = assume_spec INVNTT_L7_STMT;;

(* ------------------------------------------------------------------------- *)
(* Layer 6, a loop over 4 blocks of 8 coefficients at a time, which loads    *)
(* the coefficients one by one into the lanes and puts the results in order  *)
(* with TBL and the vectors of constants mlkem_poly_invntt_tomont_const1 to  *)
(* const8.                                                                   *)
(* ------------------------------------------------------------------------- *)

let INVNTT_L6_ADDRS_IN = CHUNK_ADDRS_FLAT 32;;

let INVNTT_L6_LO = INVNTT_LOOP_LO_RULE 1 4;;

let INVNTT_L6_HI = INVNTT_LOOP_HI_RULE 1 4;;

let INVNTT_CONSTANTS =
  map (fun k ->
    MLKEM_NATIVE_IMAGE_CONST_RULE
     (layout("mlkem_poly_invntt_tomont_const" ^ string_of_int k)) 128) (1--8);;

let INVNTT_CONSTANTS_TAC =
  MAP_EVERY (fun th -> FIRST_ASSUM(fun ath ->
      if can (term_match [] `aligned_bytes_loaded s0 (word pc)
                               mlkem_native_libmlkem_clang17_O3_mc`)
             (concl ath)
      then ASSUME_TAC(MATCH_MP th ath) else failwith "")) INVNTT_CONSTANTS;;

let invntt_l6_inv =
 `\i s. read X0 s = a /\ read X8 s = word(64 * i) /\
        read X9 s = word_add (word(pc + rodata_mlk_zetas))
                             (word(2 * (60 - 4 * i))) /\
        read X10 s = word 0xf3010000 /\
        read Q0 s = word 0xfffefffefffefffe1918111009080100 /\
        read Q1 s = word 0x1918111009080100fffefffefffefffe /\
        read Q2 s = word 0xfffefffefffefffe1b1a13120b0a0302 /\
        read Q3 s = word 0x1b1a13120b0a0302fffefffefffefffe /\
        read Q4 s = word 0xfffefffefffefffe1d1c15140d0c0504 /\
        read Q5 s = word 0x1d1c15140d0c0504fffefffefffefffe /\
        read Q6 s = word 0x4ebf4ebf4ebf4ebf /\
        read Q7 s = word 0xfffefffefffefffe1f1e17160f0e0706 /\
        read Q16 s = word 0x1f1e17160f0e0706fffefffefffefffe /\
        read Q17 s = word 0xf2fff2fff2fff2ff /\
        read Q18 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
        invntt_clang17_frame sp r d8 d9 d10 d11 d12 d13 d14 d15 x29 s /\
        (!j. j < 32 * i
             ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                 invntt_layers_c 2 (invntt_scale_c x) j) /\
        (!j. 32 * i <= j /\ j < 256
             ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                 invntt_layers_c 1 (invntt_scale_c x) j)`;;

let INVNTT_L6_GOAL =
 `!a (x:num->int16) pc sp r d8 d9 d10 d11 d12 d13 d14 d15 x29.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    nonoverlapping (a,512) (sp,688) /\
    nonoverlapping (a,512) (word pc,libmlkem_size)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_clang17_O3_mc /\
           read PC s = word (pc + mlkem_poly_invntt_tomont_loop2_exit) /\
           read X0 s = a /\
           invntt_clang17_frame sp r d8 d9 d10 d11 d12 d13 d14 d15 x29 s /\
           (!j. j < 256
                ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                    invntt_layers_c 1 (invntt_scale_c x) j))
      (\s. read PC s = word (pc + mlkem_poly_invntt_tomont_loop3_exit) /\
           read X0 s = a /\
           invntt_clang17_frame sp r d8 d9 d10 d11 d12 d13 d14 d15 x29 s /\
           (!j. j < 256
                ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                    invntt_layers_c 2 (invntt_scale_c x) j))
      (MAYCHANGE [PC; X8; X9; X10; X11; X12; X13; X14] ,,
       MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q16; Q17; Q18;
                  Q19; Q20; Q21; Q22; Q23; Q24; Q25; Q26; Q27; Q28; Q29;
                  Q30; Q31] ,,
       MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(a,512)])`;;

let INVNTT_L6_FLAG = LOOP_FLAG_RULE 64 8;;

let INVNTT_L6_PTR = ZETA_PTR_STEP_RULE 4 60;;

let INVNTT_L6_STMT =
  INVNTT_L6_GOAL;;

let INVNTT_L6 = assume_spec INVNTT_L6_STMT;;

(* ------------------------------------------------------------------------- *)
(* Layer 5, a loop over the blocks of 16 coefficients.                       *)
(* ------------------------------------------------------------------------- *)

let INVNTT_L5_LO = INVNTT_LOOP_LO_RULE 2 1;;

let INVNTT_L5_HI = INVNTT_LOOP_HI_RULE 2 1;;

let invntt_l5_inv =
 `\i s. read X0 s = a /\
        read X8 s = word_add (word(pc + rodata_mlk_zetas))
                             (word(2 * (31 - 1 * i))) /\
        read X9 s = word_add (word_add a (word(32 * i))) (word 16) /\
        read X10 s = word_add (word(16 * i)) (word 18446744073709551600) /\
        read X11 s = word 0xf3010000 /\
        read Q0 s = word 0x4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf /\
        read Q1 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
        read Q2 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
        invntt_clang17_frame sp r d8 d9 d10 d11 d12 d13 d14 d15 x29 s /\
        (!j. j < 16 * i
             ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                 invntt_layers_c 3 (invntt_scale_c x) j) /\
        (!j. 16 * i <= j /\ j < 256
             ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                 invntt_layers_c 2 (invntt_scale_c x) j)`;;

let INVNTT_L5_GOAL =
 `!a (x:num->int16) pc sp r d8 d9 d10 d11 d12 d13 d14 d15 x29.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    nonoverlapping (a,512) (sp,688) /\
    nonoverlapping (a,512) (word pc,libmlkem_size)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_clang17_O3_mc /\
           read PC s = word (pc + mlkem_poly_invntt_tomont_loop3_exit) /\
           read X0 s = a /\
           invntt_clang17_frame sp r d8 d9 d10 d11 d12 d13 d14 d15 x29 s /\
           (!j. j < 256
                ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                    invntt_layers_c 2 (invntt_scale_c x) j))
      (\s. read PC s = word (pc + mlkem_poly_invntt_tomont_loop4_exit) /\
           read X0 s = a /\
           invntt_clang17_frame sp r d8 d9 d10 d11 d12 d13 d14 d15 x29 s /\
           (!j. j < 256
                ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                    invntt_layers_c 3 (invntt_scale_c x) j))
      (MAYCHANGE [PC; X8; X9; X10; X11; X12] ,,
       MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q16; Q17] ,,
       MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(a,512)])`;;

let INVNTT_L5_FLAG_STMT =
  `!i. i < 16 ==> (val (word (16 * i):int64) < 240 <=> i + 1 < 16)`;;

let INVNTT_L5_FLAG = assume_spec INVNTT_L5_FLAG_STMT;;

let INVNTT_L5_PTR = ZETA_PTR_STEP_RULE 1 31;;

let INVNTT_L5_STMT =
  INVNTT_L5_GOAL;;

let INVNTT_L5 = assume_spec INVNTT_L5_STMT;;

(* ------------------------------------------------------------------------- *)
(* Layers 4, 3 and 2, straight-line code that keeps the coefficients in      *)
(* vector registers and spills some of them to the stack. The results are    *)
(* folded into the C model layer by layer.                                   *)
(* ------------------------------------------------------------------------- *)

(*** The equations of layer n + 1 the other way round, to fold the results
 *** of the simulation, with the sums and products in either order
 ***)

let INVNTT_FOLD_EQS n =
  List.concat (map (fun i ->
    let th = SYM(INVNTT_LAYER_EQUATION n i) in
    let th' = try GEN_REWRITE_RULE (LAND_CONV o RAND_CONV) [WORD_ADD_SYM] th
              with Failure _ ->
              GEN_REWRITE_RULE (LAND_CONV o RAND_CONV) [WORD_MUL_SYM] th in
    [th; th']) (0--255));;

let INVNTT_EQ3 = INVNTT_FOLD_EQS 3 and INVNTT_EQ4 = INVNTT_FOLD_EQS 4
and INVNTT_EQ5 = INVNTT_FOLD_EQS 5;;

let INVNTT_MERGE_TAC =
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

let INVNTT_FOLD_TAC sn eqs =
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

let INVNTT_L432_GOAL =
 `!a (x:num->int16) pc sp r d8 d9 d10 d11 d12 d13 d14 d15 x29.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    aligned 16 sp /\
    nonoverlapping (a,512) (sp,688) /\
    ALLPAIRS nonoverlapping [(a,512); (sp,688)] [(word pc,libmlkem_size)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_clang17_O3_mc /\
           read PC s = word (pc + mlkem_poly_invntt_tomont_loop4_exit) /\
           read X0 s = a /\
           invntt_clang17_frame sp r d8 d9 d10 d11 d12 d13 d14 d15 x29 s /\
           (!j. j < 256
                ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                    invntt_layers_c 3 (invntt_scale_c x) j))
      (\s. read PC s = word (pc + mlkem_poly_invntt_tomont_loop5) /\
           read X0 s = a /\ read X8 s = word 0 /\
           read X9 s = word 0xfd0a /\ read X10 s = word 0x7b0a0000 /\
           read Q13 s = word 0x4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf /\
           read Q16 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
           read Q20 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
           invntt_clang17_frame sp r d8 d9 d10 d11 d12 d13 d14 d15 x29 s /\
           (!j. j < 256
                ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                    invntt_layers_c 6 (invntt_scale_c x) j))
      (MAYCHANGE [PC; X8; X9; X10] ,,
       MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13;
                  Q14; Q15; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23; Q24; Q25;
                  Q26; Q27; Q28; Q29; Q30; Q31] ,,
       MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(a,512); memory :> bytes(sp,608)])`;;

let INVNTT_L432_STMT =
  INVNTT_L432_GOAL;;

let INVNTT_L432 = assume_spec INVNTT_L432_STMT;;

(* ------------------------------------------------------------------------- *)
(* Layer 1, a loop over 8 + 8 coefficients 128 apart, and the epilogue.      *)
(* ------------------------------------------------------------------------- *)

let CHUNK8_HALF_INPUT_SPLIT_STMT =
  `!P i. i < 16
         ==> ((!j. 8 * i <= j /\ j < 128 ==> P j) <=>
              (!j. 8 * (i + 1) <= j /\ j < 128 ==> P j) /\
              (!k. k < 8 ==> P(8 * i + k)))`;;

let CHUNK8_HALF_INPUT_SPLIT = assume_spec CHUNK8_HALF_INPUT_SPLIT_STMT;;

let INVNTT_L1_ADDRS =
  List.concat (map (fun k ->
    let sub = [mk_small_numeral k,`k:num`; mk_small_numeral(2*k),`c:num`] in
    map (fun t -> REWRITE_RULE[WORD_ADD_0] (WORD_RULE (subst sub t)))
     [`word_add a (word(2 * (8 * i + k))):int64 =
       word_add (word_add a (word(16 * i))) (word c)`;
      `word_add a (word(2 * (128 + (8 * i + k)))):int64 =
       word_add (word_add a (word(16 * i + 256))) (word c)`]) (0--7));;

let INVNTT_L1_LO_STMT =
  `!x i k. i < 16 /\ k < 8
           ==> invntt_layers_c 7 x (8 * i + k) =
               barred(word_add (invntt_layers_c 6 x (8 * i + k))
                               (invntt_layers_c 6 x (128 + (8 * i + k))))`;;

let INVNTT_L1_LO = assume_spec INVNTT_L1_LO_STMT;;

let INVNTT_L1_HI_STMT =
  `!x i k. i < 16 /\ k < 8
           ==> invntt_layers_c 7 x (128 + (8 * i + k)) =
               invntt_fqmul_c (iword(EL 1 mlk_zetas))
                (word_sub (invntt_layers_c 6 x (128 + (8 * i + k)))
                          (invntt_layers_c 6 x (8 * i + k)))`;;

let INVNTT_L1_HI = assume_spec INVNTT_L1_HI_STMT;;

let INVNTT_L1_FLAG = LOOP_FLAG_RULE 16 16;;

let INVNTT_L1_OUT_TAC =
  W(fun (asl,w) ->
    let idx = rand(rand w) in
    let hi = is_comb idx && is_comb(rator idx) &&
             lhand idx = `128` in
    let k = if hi then rand(rand idx) else rand idx in
    MP_TAC(SPECL [`invntt_scale_c x`; `i:num`; k]
                 (if hi then INVNTT_L1_HI else INVNTT_L1_LO))) THEN
  ANTS_TAC THENL [UNDISCH_TAC `i < 16` THEN ARITH_TAC;
                  DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[invntt_fqmul_c] THEN REWRITE_TAC MLK_ZETAS_ELS THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_IWORD_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  REWRITE_TAC[WORD_ADD_SYM; WORD_MUL_SYM];;

let invntt_l1_inv =
 `\i s. read X0 s = a /\ read X8 s = word(16 * i) /\
        read X9 s = word 0xfd0a /\ read X10 s = word 0x7b0a0000 /\
        read Q13 s = word 0x4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf /\
        read Q16 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
        read Q20 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
        invntt_clang17_frame sp r d8 d9 d10 d11 d12 d13 d14 d15 x29 s /\
        (!j. j < 8 * i
             ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                 invntt_layers_c 7 (invntt_scale_c x) j /\
                 read(memory :> bytes16(word_add a (word(2 * (128 + j))))) s =
                 invntt_layers_c 7 (invntt_scale_c x) (128 + j)) /\
        (!j. 8 * i <= j /\ j < 128
             ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                 invntt_layers_c 6 (invntt_scale_c x) j /\
                 read(memory :> bytes16(word_add a (word(2 * (128 + j))))) s =
                 invntt_layers_c 6 (invntt_scale_c x) (128 + j))`;;

let INVNTT_L1_STMT =
  `!a (x:num->int16) pc sp r d8 d9 d10 d11 d12 d13 d14 d15 x29.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    nonoverlapping (a,512) (sp,688) /\
    nonoverlapping (a,512) (word pc,libmlkem_size)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_clang17_O3_mc /\
           read PC s = word (pc + mlkem_poly_invntt_tomont_loop5) /\
           read X0 s = a /\ read X8 s = word 0 /\
           read X9 s = word 0xfd0a /\ read X10 s = word 0x7b0a0000 /\
           read Q13 s = word 0x4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf /\
           read Q16 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
           read Q20 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
           invntt_clang17_frame sp r d8 d9 d10 d11 d12 d13 d14 d15 x29 s /\
           (!j. j < 256
                ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                    invntt_layers_c 6 (invntt_scale_c x) j))
      (\s. read PC s = word (pc + mlkem_poly_invntt_tomont_loop5_exit) /\
           invntt_clang17_frame sp r d8 d9 d10 d11 d12 d13 d14 d15 x29 s /\
           (!j. j < 256
                ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                    invntt_layers_c 7 (invntt_scale_c x) j))
      (MAYCHANGE [PC; X8; X11] ,, MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6] ,,
       MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(a,512)])`;;

let INVNTT_L1 = assume_spec INVNTT_L1_STMT;;

(* ------------------------------------------------------------------------- *)
(* The epilogue, which restores D8-D15 and X29.                              *)
(* ------------------------------------------------------------------------- *)

let INVNTT_TAIL_STMT =
  `!a (x:num->int16) pc sp r d8 d9 d10 d11 d12 d13 d14 d15 x29.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    aligned 16 sp /\
    nonoverlapping (a,512) (sp,688) /\
    ALLPAIRS nonoverlapping [(a,512); (sp,688)] [(word pc,libmlkem_size)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_clang17_O3_mc /\
           read PC s = word (pc + mlkem_poly_invntt_tomont_loop5_exit) /\
           invntt_clang17_frame sp r d8 d9 d10 d11 d12 d13 d14 d15 x29 s /\
           (!j. j < 256
                ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                    invntt_layers_c 7 (invntt_scale_c x) j))
      (\s. read PC s = r /\
           invntt_clang17_entry (word_add sp (word 688)) r
             d8 d9 d10 d11 d12 d13 d14 d15 x29 s /\
           (!j. j < 256
                ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                    invntt_layers_c 7 (invntt_scale_c x) j))
      (MAYCHANGE [PC; SP; X29] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [events])`;;

let INVNTT_TAIL = assume_spec INVNTT_TAIL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a x pc stackpointer returnaddress.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    aligned 16 stackpointer /\
    ALL (nonoverlapping (a,512))
        [(word pc,libmlkem_size); (word_sub stackpointer (word 688),688)] /\
    nonoverlapping (word_sub stackpointer (word 688),688)
                   (word pc,libmlkem_size)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_clang17_O3_mc /\
           read PC s = word (pc + mlkem_poly_invntt_tomont) /\
           read SP s = stackpointer /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [a] s /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    x i))
      (\s. read PC s = returnaddress /\
           !i. i < 256
               ==> let zi =
                     read(memory :> bytes16(word_add a (word(2 * i)))) s in
                   (ival zi == inverse_ntt (ival o x) i) (mod &3329) /\
                   abs(ival zi) <= &26624)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
       MAYCHANGE [memory :> bytes(a,512);
                  memory :> bytes(word_sub stackpointer (word 688),688)])`;;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let INVNTT_SAFE_STEP_TAC n =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O3_EXEC [n] THEN
  MLKEM_NATIVE_ADRP_TAC;;

(*** One segment of straight-line code, from start to end ***)

let INVNTT_SAFE_SEGMENT_STEP_TAC step_tac pre_tac n fin_tac =
  REWRITE_TAC(!simulation_precanon_thms) THEN pre_tac THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  TRY INVNTT_FRAME_EXPAND_TAC THEN TRY INVNTT_ENTRY_EXPAND_TAC THEN
  MAP_EVERY step_tac (1--n) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[invntt_clang17_frame; invntt_clang17_entry] THEN
  fin_tac THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let INVNTT_SAFE_SEGMENT_TAC =
  INVNTT_SAFE_SEGMENT_STEP_TAC INVNTT_SAFE_STEP_TAC;;

(*** The end of a loop body: the branch back, then the counters ***)

let INVNTT_SAFE_BODY_FIN_TAC flag ctr_tacs =
  ASM_SIMP_TAC[flag] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  EVERY(map (fun t -> CONJ_TAC THENL [t; ALL_TAC]) ctr_tacs);;

let INVNTT_WORD_CONJS_TAC =
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE);;

let INVNTT_PTR_TAC th p =
  MATCH_MP_TAC th THEN UNDISCH_TAC p THEN ARITH_TAC;;

let INVNTT_CTR_TAC n =
  REWRITE_TAC[ARITH_RULE(subst [mk_small_numeral n,`n:num`]
                          `n * (i + 1) = n * i + n`)] THEN
  CONV_TAC WORD_RULE;;

let INVNTT_X10_TAC =
  REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
  REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN REWRITE_TAC[WORD_ADD_0];;

let invntt_sc_einv =
 `\i s. read X0 s = a /\ read X8 s = word(32 * i) /\
        invntt_clang17_entry (word_add stackpointer (word 688)) returnaddress
          d8_init d9_init d10_init d11_init d12_init d13_init d14_init
          d15_init x29_init s`;;

let invntt_l7_einv =
 `\i s. read X0 s = a /\ read X8 s = word(64 * i) /\
        read X9 s = word_add (word(pc + rodata_mlk_zetas))
                             (word(2 * (120 - 8 * i))) /\
        invntt_clang17_frame stackpointer returnaddress d8_init d9_init
          d10_init d11_init d12_init d13_init d14_init d15_init x29_init s`;;

let invntt_l6_einv =
 `\i s. read X0 s = a /\ read X8 s = word(64 * i) /\
        read X9 s = word_add (word(pc + rodata_mlk_zetas))
                             (word(2 * (60 - 4 * i))) /\
        invntt_clang17_frame stackpointer returnaddress d8_init d9_init
          d10_init d11_init d12_init d13_init d14_init d15_init x29_init s`;;

let invntt_l5_einv =
 `\i s. read X0 s = a /\
        read X8 s = word_add (word(pc + rodata_mlk_zetas))
                             (word(2 * (31 - 1 * i))) /\
        read X9 s = word_add (word_add a (word(32 * i))) (word 16) /\
        read X10 s = word_add (word(16 * i)) (word 18446744073709551600) /\
        invntt_clang17_frame stackpointer returnaddress d8_init d9_init
          d10_init d11_init d12_init d13_init d14_init d15_init x29_init s`;;

let invntt_l1_einv =
 `\i s. read X0 s = a /\ read X8 s = word(16 * i) /\
        invntt_clang17_frame stackpointer returnaddress d8_init d9_init
          d10_init d11_init d12_init d13_init d14_init d15_init x29_init s`;;

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word(pc + mlkem_poly_invntt_tomont_consts):int64`,
                       `mlkem_poly_invntt_tomont_consts_size:num`;
                       `word(pc + rodata_mlk_zetas):int64`,`256`]
    ~keep_maychanges:true
    (assoc "mlkem_reduce" subroutine_signatures)
    MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O3_EXEC;;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e a pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       ALL (nonoverlapping (a,512))
           [word pc,libmlkem_size; word_sub stackpointer (word 688),688] /\
       nonoverlapping (word_sub stackpointer (word 688),688)
         (word pc,libmlkem_size)
       ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  mlkem_native_libmlkem_clang17_O3_mc /\
                read PC s = word (pc + mlkem_poly_invntt_tomont) /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [a] s /\
                read events s = e)
           (\s. read PC s = returnaddress /\
                exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_events a pc
                         (word_sub stackpointer (word 688)) returnaddress /\
                  memaccess_inbounds e2
                   [a,512; word_sub stackpointer (word 688),688;
                    word (pc + mlkem_poly_invntt_tomont_consts),
                    mlkem_poly_invntt_tomont_consts_size;
                    word (pc + rodata_mlk_zetas),256]
                   [a,512; word_sub stackpointer (word 688),688])
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
            MAYCHANGE [memory :> bytes(a,512);
                       memory :> bytes(word_sub stackpointer (word 688),
                                       688)])`;;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
