(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* ML-DSA, the Module-Lattice-Based Digital Signature Algorithm of FIPS 204. *)
(*                                                                           *)
(* This is a specification, not an implementation: it aims to say as simply  *)
(* and abstractly as possible what the ML-DSA algorithms compute, for all    *)
(* three parameter sets, down to the bytes. It follows the style of          *)
(* common/fips203.ml for ML-KEM. Compared with the pseudocode of FIPS 204:   *)
(*                                                                           *)
(*  - All arithmetic is done in the ring R_q = Z_q[X]/(X^256 + 1) itself.    *)
(*    The NTT appears only because the matrix A is sampled in the NTT        *)
(*    domain (ExpandA). It is defined by FIPS 204 equation (2.1): the values *)
(*    of f at the 256 roots zeta^(2 * BitRev8(i) + 1) of X^256 + 1, with     *)
(*    zeta = 1753. Its inverse is simply the inverse function, so Algorithms *)
(*    41-48 (the NTT, its inverse and the NTT-domain arithmetic) are not     *)
(*    needed at all.                                                         *)
(*                                                                           *)
(*  - The rounding functions (Power2Round, Decompose, HighBits, LowBits,     *)
(*    MakeHint and UseHint) are functions on integers, via the centered      *)
(*    remainder mod+- of FIPS 204 Section 2.3, and a bound on the infinity   *)
(*    norm is a statement about all the centered coefficients.               *)
(*                                                                           *)
(*  - Byte strings are lists of bytes, and the bit packings are expressed    *)
(*    via the little-endian numeric value of a byte string, which is exactly *)
(*    the FIPS 204 bit ordering. Messages and contexts are byte strings.     *)
(*                                                                           *)
(*  - The XOFs are infinite byte streams, so the rejection samplers just     *)
(*    take the first values that are accepted, and SampleInBall is the       *)
(*    recursion over the tau steps of its shuffle.                           *)
(*                                                                           *)
(*  - Signing is the result of the first attempt, with counter kappa = l * n *)
(*    for n = 0, 1, ..., that is not rejected, or NONE if every attempt is   *)
(*    rejected (when the loop of FIPS 204 Algorithm 7 does not terminate).   *)
(*    One attempt is the function mldsa_sign_attempt, and signing from the   *)
(*    message representative mu (FIPS 204 Section 6.2, "external mu") is     *)
(*    mldsa_sign_mu; similarly mldsa_verify_mu for verification.             *)
(*                                                                           *)
(*  - Randomness (xi for key generation, rnd for signing) is an explicit     *)
(*    argument, as in the "_internal" algorithms of FIPS 204, and a pre-hash *)
(*    enters HashML-DSA only through its OID and the digest PH(M).           *)
(*                                                                           *)
(* Throughout, a parameter set is a tuple                                    *)
(* (k,l,eta,tau,lam,gamma1,gamma2,omega) as in FIPS 204 Table 1, with lam    *)
(* for lambda (q = 8380417 and d = 13 are fixed, and beta = tau * eta);      *)
(* elements of Z_q are integers in [0,q), and vectors and matrices are       *)
(* functions on indices. The generic construction poly_mod_ring of R_q is    *)
(* that of common/fips203.ml.                                                *)
(* ========================================================================= *)

needs "Library/words.ml";;
needs "Library/ringtheory.ml";;
needs "common/fips202.ml";;
needs "common/fips203.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The basic rings: Z_q with q = 8380417, Z_q[X], and R_q.                   *)
(* ------------------------------------------------------------------------- *)

let mldsa_zq = new_definition
 `mldsa_zq = integer_mod_ring 8380417`;;

let mldsa_zqx = new_definition
 `mldsa_zqx = poly_ring mldsa_zq (:1)`;;

let mldsa_X = new_definition
 `mldsa_X = poly_var mldsa_zq one`;;

let mldsa_rq = new_definition
 `mldsa_rq =
    poly_mod_ring mldsa_zq
     (ring_add mldsa_zqx (ring_pow mldsa_zqx mldsa_X 256)
               (ring_1 mldsa_zqx))`;;

(* The element of R_q with coefficient array a, reduced mod q.               *)

let mldsa_poly = new_definition
 `mldsa_poly (a:num->int) =
    \m:1->num. if m one < 256 then a(m one) rem &8380417 else &0`;;

(* "Transpose" products of vectors: u^T v = sum_{j < n} u[j] * v[j].         *)

let mldsa_dot = new_definition
 `mldsa_dot n (u:num->(1->num)->int) v =
    ring_sum mldsa_rq {j | j < n} (\j. ring_mul mldsa_rq (u j) (v j))`;;

(* ------------------------------------------------------------------------- *)
(* The NTT (FIPS 204 equation 2.1): the values at zeta^(2 * BitRev8(i) + 1), *)
(* zeta = 1753, as an array of 256 elements of Z_q. The definition of        *)
(* bitreverse8 is the same as in common/mlkem_mldsa.ml.                      *)
(* ------------------------------------------------------------------------- *)

let bitreverse8 = define
 `bitreverse8(n) = val(word_reversefields 1 (word n:8 word))`;;

let mldsa_ntt = new_definition
 `mldsa_ntt (f:(1->num)->int) i =
    poly_eval mldsa_zq f
     (ring_pow mldsa_zq (&1753) (2 * bitreverse8 i + 1))`;;

let mldsa_ntt_inv = new_definition
 `mldsa_ntt_inv (a:num->int) =
    @f. f IN ring_carrier mldsa_rq /\ !i. i < 256 ==> mldsa_ntt f i = a i`;;

(* ------------------------------------------------------------------------- *)
(* The centered remainder a mod+- m (FIPS 204 Section 2.3), in the range     *)
(* (-m/2,m/2] for even m and [-(m-1)/2,(m-1)/2] for odd m, and the bound     *)
(* ||w||_inf < b on the infinity norm of an element w of R_q (that of each   *)
(* polynomial for a vector of n polynomials).                                *)
(* ------------------------------------------------------------------------- *)

let mldsa_modpm = new_definition
 `mldsa_modpm (a:int) m =
    if &2 * (a rem &m) <= &m then a rem &m else a rem &m - &m`;;

let mldsa_norm_lt = new_definition
 `mldsa_norm_lt b (w:(1->num)->int) <=>
    !i. i < 256 ==> abs(mldsa_modpm (coeff i w) 8380417) < &b`;;

let mldsa_vec_norm_lt = new_definition
 `mldsa_vec_norm_lt n b (v:num->(1->num)->int) <=>
    !i. i < n ==> mldsa_norm_lt b (v i)`;;

(* ------------------------------------------------------------------------- *)
(* High-order and low-order bits and hints (FIPS 204 Algorithms 35-40), for  *)
(* r in Z_q given by any integer representative, with d = 13 and alpha =     *)
(* 2 * gamma2 a divisor of q - 1. The first component of the decompositions  *)
(* is r1 and the second r0. Hints are booleans.                              *)
(* ------------------------------------------------------------------------- *)

let mldsa_power2round = new_definition
 `mldsa_power2round (r:int) =
    let rp = r rem &8380417 in
    let r0 = mldsa_modpm rp 8192 in
    (rp - r0) div &8192,r0`;;

let mldsa_decompose = new_definition
 `mldsa_decompose gamma2 (r:int) =
    let rp = r rem &8380417 in
    let r0 = mldsa_modpm rp (2 * gamma2) in
    if rp - r0 = &8380416 then &0,r0 - &1
    else (rp - r0) div &(2 * gamma2),r0`;;

let mldsa_highbits = new_definition
 `mldsa_highbits gamma2 (r:int) = FST(mldsa_decompose gamma2 r)`;;

let mldsa_lowbits = new_definition
 `mldsa_lowbits gamma2 (r:int) = SND(mldsa_decompose gamma2 r)`;;

let mldsa_makehint = new_definition
 `mldsa_makehint gamma2 (z:int) (r:int) <=>
    ~(mldsa_highbits gamma2 r = mldsa_highbits gamma2 (r + z))`;;

let mldsa_usehint = new_definition
 `mldsa_usehint gamma2 h (r:int) =
    let m = &(8380416 DIV (2 * gamma2)) in
    let r1 = mldsa_highbits gamma2 r and r0 = mldsa_lowbits gamma2 r in
    if h /\ &0 < r0 then (r1 + &1) rem m
    else if h then (r1 - &1) rem m
    else r1`;;

(* ------------------------------------------------------------------------- *)
(* Bit packing (FIPS 204 Algorithms 9-19): mldsa_encode c n f is the byte    *)
(* string of the fields f(0), ..., f(n - 1) of c bits each, in order, and    *)
(* mldsa_field c b i is field i of c bits of the byte string b. For vectors  *)
(* the fields of the polynomials are concatenated, so field 256 * i + j is   *)
(* coefficient j of element i. SimpleBitPack(w,b) is mldsa_encode with c =   *)
(* bitlen b and BitPack(w,a,b) mldsa_encode of b - w with c = bitlen(a + b). *)
(* ------------------------------------------------------------------------- *)

let mldsa_bitlen = new_definition
 `mldsa_bitlen n = minimal c. n < 2 EXP c`;;

let mldsa_encode = new_definition
 `mldsa_encode c n (f:num->int) =
    bytelist_of_num ((c * n) DIV 8)
      (nsum {i | i < n} (\i. num_of_int(f i rem &2 pow c) * 2 EXP (c * i)))`;;

let mldsa_field = new_definition
 `mldsa_field c (b:byte list) i =
    &((num_of_bytelist b DIV 2 EXP (c * i)) MOD 2 EXP c):int`;;

(* The sub-list b[a : a + n] of a byte string.                               *)

let mldsa_slice = new_definition
 `mldsa_slice a n (b:byte list) = list_of_seq (\i. EL (a + i) b) n`;;

(* ------------------------------------------------------------------------- *)
(* The hints of a vector of k polynomials are a predicate h on the positions *)
(* p = 256 * i + j (coefficient j of h[i]). mldsa_hint_count h p is the      *)
(* number of hints at the positions before p. HintBitPack (Algorithm 20)     *)
(* puts the index j of the (t + 1)-th hint in byte t < omega (zero when      *)
(* there are fewer hints) and the number of hints in h[0], ..., h[i] in byte *)
(* omega + i. HintBitUnpack (Algorithm 21) checks that these numbers are     *)
(* nondecreasing and at most omega, that the indices of each polynomial are  *)
(* strictly increasing and that the unused bytes of the first omega are      *)
(* zero, and returns NONE (the symbol "bottom" of FIPS 204) if not.          *)
(* ------------------------------------------------------------------------- *)

let mldsa_hint_count = new_definition
 `mldsa_hint_count (h:num->bool) p = CARD {p' | p' < p /\ h p'}`;;

let mldsa_hintbitpack = new_definition
 `mldsa_hintbitpack k omega (h:num->bool) =
    list_of_seq
     (\t. if t < omega then
            if ?p. p < 256 * k /\ h p /\ mldsa_hint_count h p = t
            then word((@p. p < 256 * k /\ h p /\ mldsa_hint_count h p = t)
                      MOD 256)
            else word 0
          else word(mldsa_hint_count h (256 * (t - omega + 1))):byte)
     (omega + k)`;;

let mldsa_hint_start = new_definition
 `mldsa_hint_start omega (y:byte list) i =
    if i = 0 then 0 else val(EL (omega + i - 1) y)`;;

let mldsa_hint_ok = new_definition
 `mldsa_hint_ok k omega (y:byte list) <=>
    (!i. i < k ==> mldsa_hint_start omega y i <= val(EL (omega + i) y) /\
                   val(EL (omega + i) y) <= omega) /\
    (!i t. i < k /\ mldsa_hint_start omega y i < t /\
           t < val(EL (omega + i) y)
           ==> val(EL (t - 1) y) < val(EL t y)) /\
    (!t. mldsa_hint_start omega y k <= t /\ t < omega ==> EL t y = word 0)`;;

let mldsa_hintbitunpack = new_definition
 `mldsa_hintbitunpack k omega (y:byte list) =
    if mldsa_hint_ok k omega y
    then SOME(\p. p < 256 * k /\
                  ?t. mldsa_hint_start omega y (p DIV 256) <= t /\
                      t < val(EL (omega + p DIV 256) y) /\
                      val(EL t y) = p MOD 256)
    else NONE`;;

(* ------------------------------------------------------------------------- *)
(* The hash function H(str,n) = SHAKE256(str,8 * n) of FIPS 204 Section 3.7; *)
(* the XOFs H and G are the streams shake256 and shake128.                   *)
(* ------------------------------------------------------------------------- *)

let mldsa_h = new_definition
 `mldsa_h (s:byte list) n = list_of_seq (shake256 s) n`;;

(* ------------------------------------------------------------------------- *)
(* Sampling (FIPS 204 Algorithms 14, 15 and 29-34). RejNTTPoly reads the     *)
(* SHAKE128 output in groups of 3 bytes, as little-endian 23-bit numbers     *)
(* with the top bit of the last byte ignored, and returns the first 256 that *)
(* are < q (the i-th one is the one preceded by exactly i others).           *)
(* RejBoundedPoly reads the SHAKE256 output as a sequence of 4-bit           *)
(* nibbles, the low one of each byte first, and returns the first 256 that   *)
(* CoeffFromHalfByte accepts, mapped to [-eta,eta]. ExpandMask unpacks the   *)
(* polynomials of y from SHAKE256 outputs with c = 1 + bitlen(gamma1 - 1)    *)
(* bits per coefficient. ExpandA gives A itself, as the inverse NTT of the   *)
(* sampled NTT-domain matrix A^.                                             *)
(* ------------------------------------------------------------------------- *)

let mldsa_rej_ntt_poly = new_definition
 `mldsa_rej_ntt_poly (rho:byte list) =
    let s = shake128 rho in
    let c = \j. val(s(3 * j)) + 256 * val(s(3 * j + 1)) +
                65536 * (val(s(3 * j + 2)) MOD 128) in
    \i. &(c(@j. c j < 8380417 /\ CARD {j' | j' < j /\ c j' < 8380417} = i))
        :int`;;

let mldsa_rej_bounded_poly = new_definition
 `mldsa_rej_bounded_poly eta (rho:byte list) =
    let s = shake256 rho in
    let b = \t. (val(s(t DIV 2)) DIV 16 EXP (t MOD 2)) MOD 16 in
    let ok = \t. if eta = 2 then b t < 15 else b t < 9 in
    let a = \t. if eta = 2 then &2 - &(b t MOD 5) else &4 - &(b t) in
    mldsa_poly
     (\i. a(@t. ok t /\ CARD {t' | t' < t /\ ok t'} = i))`;;

let mldsa_expand_a = new_definition
 `mldsa_expand_a (rho:byte list) i j =
    mldsa_ntt_inv (mldsa_rej_ntt_poly (APPEND rho [word j; word i]))`;;

let mldsa_expand_mask = new_definition
 `mldsa_expand_mask gamma1 (rho:byte list) kappa r =
    let c = 1 + mldsa_bitlen(gamma1 - 1) in
    let v = mldsa_h (APPEND rho (bytelist_of_num 2 (kappa + r))) (32 * c) in
    mldsa_poly(\i. &gamma1 - mldsa_field c v i)`;;

(* SampleInBall: after the 8 bytes of sign bits, step k (for k < tau, with   *)
(* i = 256 - tau + k) uses the next byte j <= i: c[i] becomes c[j] and then  *)
(* c[j] becomes 1 or -1 by sign bit k. mldsa_ball_pos gives the position of  *)
(* the byte used by step k and mldsa_ball_coeffs the coefficients after k    *)
(* steps.                                                                    *)

let mldsa_ball_pos = define
 `mldsa_ball_pos tau (s:num->byte) 0 =
    (minimal p. 8 <= p /\ val(s p) <= 256 - tau) /\
  mldsa_ball_pos tau s (SUC k) =
    (minimal p. mldsa_ball_pos tau s k < p /\ val(s p) <= 256 - tau + SUC k)`;;

let mldsa_ball_coeffs = define
 `mldsa_ball_coeffs tau (s:num->byte) 0 t = &0:int /\
  mldsa_ball_coeffs tau s (SUC k) t =
    let j = val(s(mldsa_ball_pos tau s k)) in
    if t = j then
      if ODD(num_of_bytelist(list_of_seq s 8) DIV 2 EXP k) then -- &1
      else &1
    else if t = 256 - tau + k then mldsa_ball_coeffs tau s k j
    else mldsa_ball_coeffs tau s k t`;;

let mldsa_sample_in_ball = new_definition
 `mldsa_sample_in_ball tau (rho:byte list) =
    mldsa_poly(mldsa_ball_coeffs tau (shake256 rho) tau)`;;

(* ------------------------------------------------------------------------- *)
(* A parameter set is (k,l,eta,tau,lam,gamma1,gamma2,omega).                 *)
(* ------------------------------------------------------------------------- *)

new_type_abbrev("mldsa_params",`:num#num#num#num#num#num#num#num`);;

(* ------------------------------------------------------------------------- *)
(* Key generation (FIPS 204 Algorithm 6), with pkEncode and skEncode         *)
(* (Algorithms 22 and 24). t1 and t0 are integer coefficient arrays.         *)
(* ------------------------------------------------------------------------- *)

let mldsa_keygen_internal = new_definition
 `mldsa_keygen_internal
    ((k,l,eta,tau,lam,gamma1,gamma2,omega):mldsa_params) (xi:byte list) =
    let seeds = mldsa_h (APPEND xi [word k; word l]) 128 in
    let rho = mldsa_slice 0 32 seeds
    and rho' = mldsa_slice 32 64 seeds
    and key = mldsa_slice 96 32 seeds in
    let A = mldsa_expand_a rho in
    let s1 = \i. mldsa_rej_bounded_poly eta
                  (APPEND rho' (bytelist_of_num 2 i)) in
    let s2 = \i. mldsa_rej_bounded_poly eta
                  (APPEND rho' (bytelist_of_num 2 (l + i))) in
    let t = \i. ring_add mldsa_rq (mldsa_dot l (A i) s1) (s2 i) in
    let t1 = \n. FST(mldsa_power2round(coeff (n MOD 256) (t(n DIV 256)))) in
    let t0 = \n. SND(mldsa_power2round(coeff (n MOD 256) (t(n DIV 256)))) in
    let pk = APPEND rho (mldsa_encode 10 (256 * k) t1) in
    let c = mldsa_bitlen(2 * eta) in
    let s1b = mldsa_encode c (256 * l)
               (\n. &eta - mldsa_modpm (coeff (n MOD 256) (s1(n DIV 256)))
                                       8380417)
    and s2b = mldsa_encode c (256 * k)
               (\n. &eta - mldsa_modpm (coeff (n MOD 256) (s2(n DIV 256)))
                                       8380417)
    and t0b = mldsa_encode 13 (256 * k) (\n. &4096 - t0 n) in
    pk,APPEND rho (APPEND key (APPEND (mldsa_h pk 64)
                                      (APPEND s1b (APPEND s2b t0b))))`;;

(* ------------------------------------------------------------------------- *)
(* One attempt of the rejection-sampling loop of signing (FIPS 204           *)
(* Algorithm 7, lines 11-30, and sigEncode, Algorithm 26), with counter      *)
(* kappa, for the matrix A, the secret vectors s1, s2 and t0 in R_q, the     *)
(* message representative mu and the private seed rho'': NONE if the         *)
(* attempt is rejected, and otherwise the signature.                         *)
(* ------------------------------------------------------------------------- *)

let mldsa_sign_attempt = new_definition
 `mldsa_sign_attempt
    ((k,l,eta,tau,lam,gamma1,gamma2,omega):mldsa_params)
    (A:num->num->(1->num)->int) s1 s2 (t0:num->(1->num)->int)
    (mu:byte list) (rho'':byte list) kappa =
    let y = \i. mldsa_expand_mask gamma1 rho'' kappa i in
    let w = \i. mldsa_dot l (A i) y in
    let w1 = \n. mldsa_highbits gamma2 (coeff (n MOD 256) (w(n DIV 256))) in
    let ct = mldsa_h (APPEND mu (mldsa_encode
                                  (mldsa_bitlen(8380416 DIV (2 * gamma2) - 1))
                                  (256 * k) w1))
                     (lam DIV 4) in
    let c = mldsa_sample_in_ball tau ct in
    let z = \i. ring_add mldsa_rq (y i) (ring_mul mldsa_rq c (s1 i)) in
    let r = \i. ring_sub mldsa_rq (w i) (ring_mul mldsa_rq c (s2 i)) in
    let ct0 = \i. ring_mul mldsa_rq c (t0 i) in
    let h = \p. p < 256 * k /\
                mldsa_makehint gamma2
                 (--(coeff (p MOD 256) (ct0(p DIV 256))))
                 (coeff (p MOD 256)
                   (ring_add mldsa_rq (r(p DIV 256)) (ct0(p DIV 256)))) in
    let beta = tau * eta in
    if mldsa_vec_norm_lt l (gamma1 - beta) z /\
       (!i j. i < k /\ j < 256
              ==> abs(mldsa_lowbits gamma2 (coeff j (r i)))
                  < &(gamma2 - beta)) /\
       mldsa_vec_norm_lt k gamma2 ct0 /\
       mldsa_hint_count h (256 * k) <= omega
    then SOME(APPEND ct
               (APPEND (mldsa_encode (1 + mldsa_bitlen(gamma1 - 1)) (256 * l)
                         (\n. &gamma1 -
                              mldsa_modpm (coeff (n MOD 256) (z(n DIV 256)))
                                          8380417))
                       (mldsa_hintbitpack k omega h)))
    else NONE`;;

(* ------------------------------------------------------------------------- *)
(* Signing (FIPS 204 Algorithm 7), from the message representative mu        *)
(* (mldsa_sign_mu) and from the formatted message M' (mldsa_sign_internal),  *)
(* with skDecode (Algorithm 25): the first attempt kappa = l * n that is not *)
(* rejected, or NONE if every attempt is rejected.                           *)
(* ------------------------------------------------------------------------- *)

let mldsa_sign_mu = new_definition
 `mldsa_sign_mu ((k,l,eta,tau,lam,gamma1,gamma2,omega):mldsa_params)
                (sk:byte list) (mu:byte list) (rnd:byte list) =
    let c = mldsa_bitlen(2 * eta) in
    let rho = mldsa_slice 0 32 sk and key = mldsa_slice 32 32 sk in
    let s1b = mldsa_slice 128 (32 * c * l) sk
    and s2b = mldsa_slice (128 + 32 * c * l) (32 * c * k) sk
    and t0b = mldsa_slice (128 + 32 * c * (l + k)) (416 * k) sk in
    let s1 = \i. mldsa_poly(\j. &eta - mldsa_field c s1b (256 * i + j)) in
    let s2 = \i. mldsa_poly(\j. &eta - mldsa_field c s2b (256 * i + j)) in
    let t0 = \i. mldsa_poly(\j. &4096 - mldsa_field 13 t0b (256 * i + j)) in
    let rho'' = mldsa_h (APPEND key (APPEND rnd mu)) 64 in
    let att = \n. mldsa_sign_attempt (k,l,eta,tau,lam,gamma1,gamma2,omega)
                   (mldsa_expand_a rho) s1 s2 t0 mu rho'' (l * n) in
    if ?n. ~(att n = NONE) then att(minimal n. ~(att n = NONE)) else NONE`;;

let mldsa_sign_internal = new_definition
 `mldsa_sign_internal (p:mldsa_params) (sk:byte list) (m:byte list) rnd =
    mldsa_sign_mu p sk (mldsa_h (APPEND (mldsa_slice 64 64 sk) m) 64) rnd`;;

(* ------------------------------------------------------------------------- *)
(* Verification (FIPS 204 Algorithm 8), from mu and from M', with pkDecode   *)
(* and sigDecode (Algorithms 23 and 27) and the length checks of FIPS 204    *)
(* Section 3.6.2. t1 is used as t1 * 2^d in R_q.                             *)
(* ------------------------------------------------------------------------- *)

let mldsa_verify_mu = new_definition
 `mldsa_verify_mu ((k,l,eta,tau,lam,gamma1,gamma2,omega):mldsa_params)
                  (pk:byte list) (mu:byte list) (sg:byte list) <=>
    let c = 1 + mldsa_bitlen(gamma1 - 1) in
    let rho = mldsa_slice 0 32 pk and t1b = mldsa_slice 32 (320 * k) pk in
    let t1 = \i. mldsa_poly(\j. &8192 * mldsa_field 10 t1b (256 * i + j)) in
    let ct = mldsa_slice 0 (lam DIV 4) sg
    and zb = mldsa_slice (lam DIV 4) (32 * c * l) sg
    and hb = mldsa_slice (lam DIV 4 + 32 * c * l) (omega + k) sg in
    let z = \i. mldsa_poly(\j. &gamma1 - mldsa_field c zb (256 * i + j)) in
    LENGTH pk = 32 + 320 * k /\
    LENGTH sg = lam DIV 4 + 32 * c * l + omega + k /\
    match mldsa_hintbitunpack k omega hb with
      NONE -> F
    | SOME h ->
       let cc = mldsa_sample_in_ball tau ct in
       let w = \i. ring_sub mldsa_rq (mldsa_dot l (mldsa_expand_a rho i) z)
                                     (ring_mul mldsa_rq cc (t1 i)) in
       let w1 = \n. mldsa_usehint gamma2 (h n)
                     (coeff (n MOD 256) (w(n DIV 256))) in
       mldsa_vec_norm_lt l (gamma1 - tau * eta) z /\
       mldsa_h (APPEND mu (mldsa_encode
                            (mldsa_bitlen(8380416 DIV (2 * gamma2) - 1))
                            (256 * k) w1))
               (lam DIV 4) = ct`;;

let mldsa_verify_internal = new_definition
 `mldsa_verify_internal (p:mldsa_params) (pk:byte list) (m:byte list) sg <=>
    mldsa_verify_mu p pk (mldsa_h (APPEND (mldsa_h pk 64) m) 64) sg`;;

(* ------------------------------------------------------------------------- *)
(* ML-DSA (FIPS 204 Algorithms 1, 2 and 3), with the random seeds as         *)
(* arguments, and NONE (the symbol "bottom") when the context is too long.   *)
(* ------------------------------------------------------------------------- *)

let mldsa_keygen = new_definition
 `mldsa_keygen (p:mldsa_params) (xi:byte list) = mldsa_keygen_internal p xi`;;

let mldsa_sign = new_definition
 `mldsa_sign (p:mldsa_params) (sk:byte list) (m:byte list) (ctx:byte list)
             (rnd:byte list) =
    if 255 < LENGTH ctx then NONE
    else mldsa_sign_internal p sk
          (APPEND (CONS (word 0) (CONS (word(LENGTH ctx)) ctx)) m) rnd`;;

let mldsa_verify = new_definition
 `mldsa_verify (p:mldsa_params) (pk:byte list) (m:byte list) (sg:byte list)
               (ctx:byte list) =
    if 255 < LENGTH ctx then NONE
    else SOME(mldsa_verify_internal p pk
               (APPEND (CONS (word 0) (CONS (word(LENGTH ctx)) ctx)) m) sg)`;;

(* ------------------------------------------------------------------------- *)
(* HashML-DSA (FIPS 204 Algorithms 4 and 5), given the DER encoding oid of   *)
(* the OID of the pre-hash function and the digest ph = PH(M). Signing is    *)
(* NONE and verification false when the context is too long. The OIDs        *)
(* 2.16.840.1.101.3.4.2.n of the hash functions of FIPS 180 and FIPS 202     *)
(* are mldsa_oid n: n = 1, 2, 3, 4, 5, 6 for SHA-256, SHA-384, SHA-512,      *)
(* SHA-224, SHA-512/224 and SHA-512/256, n = 7, 8, 9, 10 for SHA3-224,       *)
(* SHA3-256, SHA3-384 and SHA3-512, and n = 11, 12 for SHAKE128 and          *)
(* SHAKE256 (with digests of 256 and 512 bits).                              *)
(* ------------------------------------------------------------------------- *)

let mldsa_oid = new_definition
 `mldsa_oid n =
    [word 0x06; word 0x09; word 0x60; word 0x86; word 0x48; word 0x01;
     word 0x65; word 0x03; word 0x04; word 0x02; word n]:byte list`;;

let hash_mldsa_sign = new_definition
 `hash_mldsa_sign (p:mldsa_params) (sk:byte list) (oid:byte list)
                  (ph:byte list) (ctx:byte list) (rnd:byte list) =
    if 255 < LENGTH ctx then NONE
    else mldsa_sign_internal p sk
          (APPEND (CONS (word 1) (CONS (word(LENGTH ctx)) ctx))
                  (APPEND oid ph)) rnd`;;

let hash_mldsa_verify = new_definition
 `hash_mldsa_verify (p:mldsa_params) (pk:byte list) (oid:byte list)
                    (ph:byte list) (sg:byte list) (ctx:byte list) <=>
    LENGTH ctx <= 255 /\
    mldsa_verify_internal p pk
     (APPEND (CONS (word 1) (CONS (word(LENGTH ctx)) ctx)) (APPEND oid ph))
     sg`;;

(* ------------------------------------------------------------------------- *)
(* The three parameter sets (k,l,eta,tau,lam,gamma1,gamma2,omega) of         *)
(* FIPS 204 Table 1.                                                         *)
(* ------------------------------------------------------------------------- *)

let mldsa44 = new_definition
 `mldsa44 = (4,4,2,39,128,131072,95232,80):mldsa_params`;;

let mldsa65 = new_definition
 `mldsa65 = (6,5,4,49,192,524288,261888,55):mldsa_params`;;

let mldsa87 = new_definition
 `mldsa87 = (8,7,2,60,256,524288,261888,75):mldsa_params`;;

(* Restore the default setting for anything loaded later.                    *)

type_invention_error := false;;
