(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* A functional specification of the arithmetic of mldsa-native's portable   *)
(* C implementation: the reductions of reduce.h and the operations on single *)
(* polynomials of poly.c.                                                    *)
(*                                                                           *)
(* This is not a specification of ML-DSA in the sense of FIPS 204. It states *)
(* exactly what each C function computes, as HOL functions on machine words, *)
(* following the C code operation by operation, so that the proofs about     *)
(* the compiled code can show that it computes the same values. Composed,    *)
(* these functions give one version of ML-DSA; relating that version to      *)
(* FIPS 204 (congruences modulo q, bounds, the NTT as an evaluation) is a    *)
(* separate step that does not involve the compiled code.                    *)
(*                                                                           *)
(* Conventions:                                                              *)
(*                                                                           *)
(*  - The C types int32_t and int64_t are the HOL types int32 and int64, and *)
(*    the C arithmetic is word arithmetic. Where the C code relies on the    *)
(*    absence of signed overflow (which the CBMC contracts of mldsa-native   *)
(*    establish), the word operations wrap around and agree with C           *)
(*    whenever C is defined.                                                 *)
(*                                                                           *)
(*  - A polynomial (mld_poly, 256 coefficients of type int32_t) is a         *)
(*    function x:num->int32, with coefficient i being x i for i < 256. The   *)
(*    values of x beyond 255 do not matter, and the functions here define    *)
(*    them in the same pointwise way as the others.                          *)
(*                                                                           *)
(*  - Names follow the C functions, with the mld_ prefix of mldsa-native's   *)
(*    internal names, e.g. mld_poly_reduce for mld_poly_reduce.              *)
(* ========================================================================= *)

needs "Library/words.ml";;

(* ------------------------------------------------------------------------- *)
(* The parameters common to all parameter sets (params.h).                   *)
(* ------------------------------------------------------------------------- *)

(*** MLDSA_Q = 8380417 = 2^23 - 2^13 + 1, MLDSA_N = 256, MLDSA_D = 13 ***)

let mldsa_q = new_definition
 `mldsa_q = 8380417`;;

(* ------------------------------------------------------------------------- *)
(* The reductions of reduce.h.                                               *)
(* ------------------------------------------------------------------------- *)

(*** mld_montgomery_reduce(a): with t = (int32)((uint32)a * QINV) for   ***)
(*** QINV = 58728449 = q^-1 mod 2^32, the high 32 bits of a - t * q,    ***)
(*** which is divisible by 2^32. As the result is truncated to 32 bits, ***)
(*** it is bits 32..63 of the 64-bit difference.                        ***)

let mld_montgomery_reduce = new_definition
 `mld_montgomery_reduce (a:int64):int32 =
    let t:int32 = word_mul (word_zx a) (word 58728449) in
    word_subword (word_sub a (word_mul (word_sx t) (word 8380417))) (32,32)`;;

(*** mld_reduce32(a) = a - ((a + 2^22) >> 23) * q, the shift arithmetic ***)

let mld_reduce32 = new_definition
 `mld_reduce32 (a:int32):int32 =
    word_sub a
     (word_mul (word_ishr (word_add a (word 4194304)) 23) (word 8380417))`;;

(*** mld_caddq(a): a + q if a is negative, a otherwise ***)

let mld_caddq = new_definition
 `mld_caddq (a:int32):int32 =
    if ival a < &0 then word_add a (word 8380417) else a`;;

(*** mld_fqmul(a,b) = mld_montgomery_reduce((int64)a * b) (poly.c) ***)

let mld_fqmul = new_definition
 `mld_fqmul (a:int32) (b:int32):int32 =
    mld_montgomery_reduce (word_mul (word_sx a) (word_sx b))`;;

(* ------------------------------------------------------------------------- *)
(* Operations on polynomials (poly.c) that act on each coefficient.          *)
(* ------------------------------------------------------------------------- *)

let mld_poly_reduce = new_definition
 `mld_poly_reduce (a:num->int32) = \i. mld_reduce32 (a i)`;;

let mld_poly_caddq = new_definition
 `mld_poly_caddq (a:num->int32) = \i. mld_caddq (a i)`;;

let mld_poly_add = new_definition
 `mld_poly_add (a:num->int32) (b:num->int32) = \i. word_add (a i) (b i)`;;

let mld_poly_sub = new_definition
 `mld_poly_sub (a:num->int32) (b:num->int32) = \i. word_sub (a i) (b i)`;;

(*** mld_poly_shiftl: multiplication by 2^MLDSA_D = 2^13 ***)

let mld_poly_shiftl = new_definition
 `mld_poly_shiftl (a:num->int32) = \i. word_mul (a i) (word 8192)`;;

(* ------------------------------------------------------------------------- *)
(* The table mld_zetas of zetas.inc: entry k is the Montgomery form          *)
(* mont * zeta^brv8(k) mod q, centred, of a power of the root of unity       *)
(* zeta = 1753 (entry 0 is not used). mld_zeta k is entry k as an int32.     *)
(* ------------------------------------------------------------------------- *)

let mld_zetas = define
 `mld_zetas:int list =
   [&0; &25847; -- &2608894; -- &518909; &237124; -- &777960; -- &876248;
    &466468; &1826347; &2353451; -- &359251; -- &2091905; &3119733;
    -- &2884855; &3111497; &2680103; &2725464; &1024112; -- &1079900;
    &3585928; -- &549488; -- &1119584; &2619752; -- &2108549; -- &2118186;
    -- &3859737; -- &1399561; -- &3277672; &1757237; -- &19422; &4010497;
    &280005; &2706023; &95776; &3077325; &3530437; -- &1661693;
    -- &3592148; -- &2537516; &3915439; -- &3861115; -- &3043716; &3574422;
    -- &2867647; &3539968; -- &300467; &2348700; -- &539299; -- &1699267;
    -- &1643818; &3505694; -- &3821735; &3507263; -- &2140649; -- &1600420;
    &3699596; &811944; &531354; &954230; &3881043; &3900724; -- &2556880;
    &2071892; -- &2797779; -- &3930395; -- &1528703; -- &3677745;
    -- &3041255; -- &1452451; &3475950; &2176455; -- &1585221; -- &1257611;
    &1939314; -- &4083598; -- &1000202; -- &3190144; -- &3157330;
    -- &3632928; &126922; &3412210; -- &983419; &2147896; &2715295;
    -- &2967645; -- &3693493; -- &411027; -- &2477047; -- &671102;
    -- &1228525; -- &22981; -- &1308169; -- &381987; &1349076; &1852771;
    -- &1430430; -- &3343383; &264944; &508951; &3097992; &44288;
    -- &1100098; &904516; &3958618; -- &3724342; -- &8578; &1653064;
    -- &3249728; &2389356; -- &210977; &759969; -- &1316856; &189548;
    -- &3553272; &3159746; -- &1851402; -- &2409325; -- &177440; &1315589;
    &1341330; &1285669; -- &1584928; -- &812732; -- &1439742; -- &3019102;
    -- &3881060; -- &3628969; &3839961; &2091667; &3407706; &2316500;
    &3817976; -- &3342478; &2244091; -- &2446433; -- &3562462; &266997;
    &2434439; -- &1235728; &3513181; -- &3520352; -- &3759364; -- &1197226;
    -- &3193378; &900702; &1859098; &909542; &819034; &495491; -- &1613174;
    -- &43260; -- &522500; -- &655327; -- &3122442; &2031748; &3207046;
    -- &3556995; -- &525098; -- &768622; -- &3595838; &342297; &286988;
    -- &2437823; &4108315; &3437287; -- &3342277; &1735879; &203044;
    &2842341; &2691481; -- &2590150; &1265009; &4055324; &1247620;
    &2486353; &1595974; -- &3767016; &1250494; &2635921; -- &3548272;
    -- &2994039; &1869119; &1903435; -- &1050970; -- &1333058; &1237275;
    -- &3318210; -- &1430225; -- &451100; &1312455; &3306115; -- &1962642;
    -- &1279661; &1917081; -- &2546312; -- &1374803; &1500165; &777191;
    &2235880; &3406031; -- &542412; -- &2831860; -- &1671176; -- &1846953;
    -- &2584293; -- &3724270; &594136; -- &3776993; -- &2013608; &2432395;
    &2454455; -- &164721; &1957272; &3369112; &185531; -- &1207385;
    -- &3183426; &162844; &1616392; &3014001; &810149; &1652634;
    -- &3694233; -- &1799107; -- &3038916; &3523897; &3866901; &269760;
    &2213111; -- &975884; &1717735; &472078; -- &426683; &1723600;
    -- &1803090; &1910376; -- &1667432; -- &1104333; -- &260646;
    -- &3833893; -- &2939036; -- &2235985; -- &420899; -- &2286327;
    &183443; -- &976891; &1612842; -- &3545687; -- &554416; &3919660;
    -- &48306; -- &1362209; &3937738; &1400424; -- &846154; &1976782]`;;

let mld_zeta = new_definition
 `mld_zeta k:int32 = iword(EL k mld_zetas)`;;

(* ------------------------------------------------------------------------- *)
(* The forward NTT (mld_poly_ntt_c in poly.c), in the order of the C code.   *)
(* It has 8 layers; layer l + 1 (for l = 0, ..., 7) consists of 2^l blocks   *)
(* of 2 * len consecutive coefficients with len = 2^(7 - l). Block b starts  *)
(* at 2 * len * b and uses zeta = mld_zeta(2^l + b): for each j of its first *)
(* half, with t = mld_fqmul r[j + len] zeta, it sets r[j + len] = r[j] - t   *)
(* and r[j] = r[j] + t (mld_ntt_butterfly_block). As the pairs of a block    *)
(* are disjoint, mld_ntt_block gives the whole block at once.                *)
(* ------------------------------------------------------------------------- *)

let mld_ntt_block = define
 `mld_ntt_block (zeta:int32) start len (r:num->int32) i =
    if start <= i /\ i < start + len
    then word_add (r i) (mld_fqmul (r(i + len)) zeta)
    else if start + len <= i /\ i < start + 2 * len
    then word_sub (r(i - len)) (mld_fqmul (r i) zeta)
    else r i`;;

let mld_ntt_blocks = define
 `mld_ntt_blocks l 0 (r:num->int32) = r /\
  mld_ntt_blocks l (SUC b) r =
    mld_ntt_block (mld_zeta(2 EXP l + b))
                  (2 * 2 EXP (7 - l) * b) (2 EXP (7 - l))
                  (mld_ntt_blocks l b r)`;;

let mld_ntt_layers = define
 `mld_ntt_layers 0 (x:num->int32) = x /\
  mld_ntt_layers (SUC l) x = mld_ntt_blocks l (2 EXP l) (mld_ntt_layers l x)`;;

let mld_poly_ntt = new_definition
 `mld_poly_ntt (x:num->int32) = mld_ntt_layers 8 x`;;

(* ------------------------------------------------------------------------- *)
(* The inverse NTT (mld_poly_invntt_tomont_c in poly.c). Its layers are done *)
(* in the order 8, ..., 1; layer m consists of 2^(m - 1) blocks of 2 * len   *)
(* coefficients with len = 2^(8 - m), and block b uses                       *)
(* zeta = -mld_zeta(2^m - 1 - b): for each j of its first half it sets       *)
(* r[j] = t + r[j + len] and r[j + len] = mld_fqmul (t - r[j + len]) zeta,   *)
(* where t is the old r[j]. mld_invntt_layers n does the first n layers,     *)
(* and the result is each coefficient scaled by mld_fqscale, a Montgomery    *)
(* multiplication by 41978 = 2^56 mod q (mont^2 / 256 with mont = 2^32).     *)
(* ------------------------------------------------------------------------- *)

let mld_invntt_block = define
 `mld_invntt_block (zeta:int32) start len (r:num->int32) i =
    if start <= i /\ i < start + len
    then word_add (r i) (r(i + len))
    else if start + len <= i /\ i < start + 2 * len
    then mld_fqmul (word_sub (r(i - len)) (r i)) zeta
    else r i`;;

let mld_invntt_blocks = define
 `mld_invntt_blocks m 0 (r:num->int32) = r /\
  mld_invntt_blocks m (SUC b) r =
    mld_invntt_block (word_neg(mld_zeta(2 EXP m - 1 - b)))
                     (2 * 2 EXP (8 - m) * b) (2 EXP (8 - m))
                     (mld_invntt_blocks m b r)`;;

let mld_invntt_layers = define
 `mld_invntt_layers 0 (x:num->int32) = x /\
  mld_invntt_layers (SUC n) x =
    mld_invntt_blocks (8 - n) (2 EXP (7 - n)) (mld_invntt_layers n x)`;;

let mld_fqscale = new_definition
 `mld_fqscale (a:int32) =
    mld_montgomery_reduce (word_mul (word_sx a) (word 41978))`;;

let mld_poly_invntt_tomont = new_definition
 `mld_poly_invntt_tomont (x:num->int32) =
    \i. mld_fqscale (mld_invntt_layers 8 x i)`;;

(* ------------------------------------------------------------------------- *)
(* Pointwise Montgomery multiplication and the splitting by 2^13 (poly.c and *)
(* mld_power2round of rounding.h): a1 = (a + 2^12 - 1) >> 13 and             *)
(* a0 = a - a1 * 2^13.                                                       *)
(* ------------------------------------------------------------------------- *)

let mld_poly_pointwise_montgomery = new_definition
 `mld_poly_pointwise_montgomery (a:num->int32) (b:num->int32) =
    \i. mld_montgomery_reduce (word_mul (word_sx (a i)) (word_sx (b i)))`;;

let mld_power2round_hi = new_definition
 `mld_power2round_hi (a:int32):int32 = word_ishr (word_add a (word 4095)) 13`;;

let mld_power2round_lo = new_definition
 `mld_power2round_lo (a:int32):int32 =
    word_sub a (word_shl (mld_power2round_hi a) 13)`;;

let mld_poly_power2round_hi = new_definition
 `mld_poly_power2round_hi (a:num->int32) = \i. mld_power2round_hi (a i)`;;

let mld_poly_power2round_lo = new_definition
 `mld_poly_power2round_lo (a:num->int32) = \i. mld_power2round_lo (a i)`;;

(* ------------------------------------------------------------------------- *)
(* The constant-time helpers of ct.h on 32-bit values, as the selections     *)
(* they implement: mld_ct_abs_i32 and mld_ct_cmask_neg_i32 (whose uint32_t   *)
(* result is given as an int32 with the same bits).                          *)
(* ------------------------------------------------------------------------- *)

let mld_ct_abs = new_definition
 `mld_ct_abs (x:int32) = if ival x < &0 then word_neg x else x`;;

let mld_ct_cmask_neg = new_definition
 `mld_ct_cmask_neg (x:int32):int32 =
    if ival x < &0 then word 4294967295 else word 0`;;

(* ------------------------------------------------------------------------- *)
(* The norm check of poly.c: all ones if some coefficient a has              *)
(* B - 1 - |a| < 0 (in 32-bit arithmetic), zero otherwise.                   *)
(* ------------------------------------------------------------------------- *)

let mld_poly_chknorm = new_definition
 `mld_poly_chknorm (a:num->int32) (B:int32):int32 =
    if ?i. i < 256 /\
           ival(word_sub (word_sub B (word 1)) (mld_ct_abs(a i))) < &0
    then word 4294967295 else word 0`;;
