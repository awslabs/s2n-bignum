(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* ML-KEM, the Module-Lattice-Based Key-Encapsulation Mechanism of FIPS 203. *)
(*                                                                           *)
(* This file is a specification, not an implementation: it says as simply    *)
(* and abstractly as possible what the ML-KEM algorithms compute, for all    *)
(* three parameter sets, down to the bytes. Properties of the definitions    *)
(* are in properties/; a second model that follows the pseudocode step by    *)
(* step, and its proved equivalence with this file, are in generated/.       *)
(*                                                                           *)
(* References                                                                *)
(*                                                                           *)
(* - [FIPS203]                                                               *)
(*   FIPS 203 Module-Lattice-Based Key-Encapsulation Mechanism Standard      *)
(*   National Institute of Standards and Technology                          *)
(*   https://csrc.nist.gov/pubs/fips/203/final                               *)
(*                                                                           *)
(* - [FIPS202]                                                               *)
(*   FIPS 202 SHA-3 Standard: Permutation-Based Hash and Extendable-Output   *)
(*   Functions, National Institute of Standards and Technology               *)
(*   (see common/fips202/fips202.ml)                                         *)
(*                                                                           *)
(* Each definition cites what it implements as @[FIPS203, Algorithm n, name] *)
(* or by section or equation. Compared with the pseudocode:                  *)
(*                                                                           *)
(*  - All arithmetic is done in the ring R_q = Z_q[X]/(X^256 + 1) itself.    *)
(*    The NTT appears only because the standard uses NTT-domain values in    *)
(*    the key formats and in the sampling of the matrix A, and it is defined *)
(*    by FIPS 203's own equations (4.12) and (4.13): the coefficient pairs   *)
(*    of f mod (X^2 - zeta^(2 * BitRev7(i) + 1)). Its inverse is simply the  *)
(*    inverse function. Algorithms 9-12 (NTT, NTT^-1, MultiplyNTTs and       *)
(*    BaseCaseMultiply) are therefore not needed at all; properties/         *)
(*    kpke_ntt_domain.ml proves that the NTT-domain formulation of FIPS 203  *)
(*    Algorithms 13-15 gives the same results (KPKE_KEYGEN_FIPS etc.).       *)
(*                                                                           *)
(*  - Byte strings are lists of bytes, and the various bit-level encodings   *)
(*    are uniformly expressed via the little-endian numeric value of a byte  *)
(*    string, which is exactly the FIPS 203 bit ordering.                    *)
(*                                                                           *)
(*  - The XOF is viewed as an infinite byte stream, so SampleNTT just takes  *)
(*    the first 256 values < q in the sequence of 12-bit fields.             *)
(*                                                                           *)
(*  - Randomness (d and z for key generation, m for encapsulation) is an     *)
(*    explicit argument, as in the internal algorithms of FIPS 203, and the  *)
(*    input checks of Section 7 are separate predicates.                     *)
(*                                                                           *)
(* Throughout, a parameter set is a tuple (k,eta1,eta2,du,dv), elements of   *)
(* Z_q are integers in [0,q), and vectors/matrices are functions on indices. *)
(* ========================================================================= *)

needs "Library/words.ml";;
needs "Library/ringtheory.ml";;
needs "common/bitmap.ml";;
needs "common/fips202/fips202.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Parameter sets (k,eta1,eta2,du,dv).                                       *)
(* Implements @[FIPS203, Section 8, Table 2].                                *)
(* ------------------------------------------------------------------------- *)

new_type_abbrev("mlkem_params",`:num#num#num#num#num`);;

let mlkem512 = new_definition
 `mlkem512 = (2,3,2,10,4)`;;

let mlkem768 = new_definition
 `mlkem768 = (3,2,2,10,4)`;;

let mlkem1024 = new_definition
 `mlkem1024 = (4,2,2,11,5)`;;

(* ------------------------------------------------------------------------- *)
(* The rings: Z_q with q = 3329, Z_q[X], and R_q = Z_q[X]/(X^256 + 1).       *)
(*                                                                           *)
(* poly_mod_ring is a generic construction, not part of FIPS 203: the ring   *)
(* of remainders modulo a polynomial m, whose elements are the polynomials p *)
(* with poly_rem p m = p (i.e. those of degree < deg(m) when the leading     *)
(* coefficient of m is a unit) and whose operations are the polynomial       *)
(* operations followed by reduction mod m. When the leading coefficient of m *)
(* is a unit, this is isomorphic to the quotient of poly_ring r (:1) by the  *)
(* ideal generated by m (theorem POLY_MOD_RING_ISOMORPHIC_QUOTIENT in        *)
(* properties/poly_remainder.ml).                                            *)
(* ------------------------------------------------------------------------- *)

let poly_mod_ring = new_definition
 `poly_mod_ring (r:A ring) m =
    ring({p | p IN ring_carrier(poly_ring r (:1)) /\ poly_rem r p m = p},
         poly_rem r (ring_0(poly_ring r (:1))) m,
         poly_rem r (ring_1(poly_ring r (:1))) m,
         (\p. poly_rem r (ring_neg (poly_ring r (:1)) p) m),
         (\p q. poly_rem r (ring_add (poly_ring r (:1)) p q) m),
         (\p q. poly_rem r (ring_mul (poly_ring r (:1)) p q) m))`;;

let mlkem_zq = new_definition
 `mlkem_zq = integer_mod_ring 3329`;;

let mlkem_zqx = new_definition
 `mlkem_zqx = poly_ring mlkem_zq (:1)`;;

let mlkem_X = new_definition
 `mlkem_X = poly_var mlkem_zq one`;;

let mlkem_rq = new_definition
 `mlkem_rq =
    poly_mod_ring mlkem_zq
     (ring_add mlkem_zqx (ring_pow mlkem_zqx mlkem_X 256)
               (ring_1 mlkem_zqx))`;;

(* The element of R_q with coefficient array a, reduced mod q.               *)

let mlkem_poly = new_definition
 `mlkem_poly (a:num->int) =
    \m:1->num. if m one < 256 then a(m one) rem &3329 else &0`;;

(* The product u^T v of two vectors of k elements of R_q: sum_{j < k} u[j] * *)
(* v[j]. (The pseudocode writes it in the NTT domain; see the notes above.)  *)

let mlkem_dot = new_definition
 `mlkem_dot k (u:num->(1->num)->int) v =
    ring_sum mlkem_rq {j | j < k} (\j. ring_mul mlkem_rq (u j) (v j))`;;

(* ------------------------------------------------------------------------- *)
(* The NTT: the residues of f modulo X^2 - zeta^(2 * BitRev7(i) + 1) with    *)
(* zeta = 17, as an array of 256 coefficients.                               *)
(* Implements FIPS 203 equations (4.12) and (4.13), in place of Algorithms 9 *)
(* and 10. BitRev7 is bitreverse7 of common/bitmap.ml, which is the same as *)
(* the reversal of a 7-bit word on [0,128) (BITREVERSE7_ALT) and is shared   *)
(* with common/mlkem_mldsa.ml. mlkem_ntt applies it only to i DIV 2 < 128.   *)
(* ------------------------------------------------------------------------- *)

let mlkem_ntt = new_definition
 `mlkem_ntt (f:(1->num)->int) i =
    coeff (i MOD 2)
          (poly_rem mlkem_zq f
             (ring_sub mlkem_zqx (ring_pow mlkem_zqx mlkem_X 2)
               (poly_const mlkem_zq
                 (ring_pow mlkem_zq (&17) (2 * bitreverse7(i DIV 2) + 1)))))`;;

(* The inverse of the NTT on arrays of 256 coefficients: the element of R_q  *)
(* whose NTT is a (it exists and is unique when a is reduced mod q).         *)

let mlkem_ntt_inv = new_definition
 `mlkem_ntt_inv (a:num->int) =
    @f. f IN ring_carrier mlkem_rq /\ !i. i < 256 ==> mlkem_ntt f i = a i`;;

(* ------------------------------------------------------------------------- *)
(* Rounding, compression and decompression.                                  *)
(* Implements FIPS 203 equations (4.7) and (4.8).                            *)
(* mlkem_round(a,b) is the integer closest to a / b, rounding up on ties.    *)
(* ------------------------------------------------------------------------- *)

let mlkem_round = new_definition
 `mlkem_round(a:int,b:int) = (&2 * a + b) div (&2 * b)`;;

let mlkem_compress = new_definition
 `mlkem_compress d (x:int) = mlkem_round(&2 pow d * x,&3329) rem &2 pow d`;;

let mlkem_decompress = new_definition
 `mlkem_decompress d (y:int) = mlkem_round(&3329 * y,&2 pow d)`;;

(* ------------------------------------------------------------------------- *)
(* Encoding and decoding between arrays of d-bit fields and byte strings.    *)
(* mlkem_encode implements @[FIPS203, Algorithm 5, ByteEncode_d] and         *)
(* mlkem_decode @[FIPS203, Algorithm 6, ByteDecode_d], including the bit     *)
(* conversions of Algorithms 3 and 4 (BitsToBytes, BytesToBits); decoding    *)
(* with d = 12 also reduces mod q. For a vector of k polynomials the fields  *)
(* are simply concatenated, so field 256 * i + j corresponds to coefficient  *)
(* j of element i.                                                           *)
(* ------------------------------------------------------------------------- *)

let mlkem_encode = new_definition
 `mlkem_encode d n (f:num->int) =
    bytelist_of_num ((d * n) DIV 8)
      (nsum {i | i < n} (\i. num_of_int(f i rem &2 pow d) * 2 EXP (d * i)))`;;

let mlkem_decode = new_definition
 `mlkem_decode d (b:byte list) i =
    let x = &((num_of_bytelist b DIV 2 EXP (d * i)) MOD 2 EXP d):int in
    if d = 12 then x rem &3329 else x`;;

(* The sub-list b[a : a + n] of a byte string, the slice notation of the     *)
(* pseudocode.                                                               *)

let mlkem_slice = new_definition
 `mlkem_slice a n (b:byte list) = list_of_seq (\i. EL (a + i) b) n`;;

(* ------------------------------------------------------------------------- *)
(* The cryptographic functions PRF_eta, H, J, G and XOF.                     *)
(* Implements @[FIPS203, Section 4.1], on top of @[FIPS202]                  *)
(* (common/fips202/fips202.ml).                                              *)
(* ------------------------------------------------------------------------- *)

let mlkem_prf = new_definition
 `mlkem_prf eta (s:byte list) (b:byte) =
    list_of_seq (shake256 (APPEND s [b])) (64 * eta)`;;

let mlkem_h = new_definition
 `mlkem_h (s:byte list) = sha3_256 s`;;

let mlkem_j = new_definition
 `mlkem_j (s:byte list) = list_of_seq (shake256 s) 32`;;

let mlkem_g = new_definition
 `mlkem_g (c:byte list) =
    mlkem_slice 0 32 (sha3_512 c),mlkem_slice 32 32 (sha3_512 c)`;;

let mlkem_xof = new_definition
 `mlkem_xof (b:byte list) = shake128 b`;;

(* ------------------------------------------------------------------------- *)
(* Sampling.                                                                 *)
(*                                                                           *)
(* mlkem_sample_ntt implements @[FIPS203, Algorithm 7, SampleNTT]: it reads  *)
(* the XOF output as a little-endian bit stream cut into 12-bit integers,    *)
(* and returns the first 256 of those that are < q (the i-th one is the one  *)
(* preceded by exactly i others). That there are 256 of them is shown in     *)
(* properties/sampling.ml.                                                   *)
(*                                                                           *)
(* mlkem_cbd implements @[FIPS203, Algorithm 8, SamplePolyCBD_eta]: it makes *)
(* coefficient i the difference of the numbers of 1 bits in two consecutive  *)
(* eta-bit blocks.                                                           *)
(* ------------------------------------------------------------------------- *)

let mlkem_xof_field = new_definition
 `mlkem_xof_field (s:num->byte) j =
    nsum {t | t < 12}
     (\t. bitval(bit ((12 * j + t) MOD 8) (s((12 * j + t) DIV 8))) *
          2 EXP t)`;;

let mlkem_sample_ntt = new_definition
 `mlkem_sample_ntt (b:byte list) =
    let c = mlkem_xof_field (mlkem_xof b) in
    \i. &(c(@j. c j < 3329 /\ CARD {j' | j' < j /\ c j' < 3329} = i)):int`;;

let mlkem_cbd = new_definition
 `mlkem_cbd eta (b:byte list) =
    let bit = \t. (num_of_bytelist b DIV 2 EXP t) MOD 2 in
    mlkem_poly
     (\i. &(nsum {j | j < eta} (\j. bit(2 * eta * i + j))) -
          &(nsum {j | j < eta} (\j. bit(2 * eta * i + eta + j))))`;;

(* ------------------------------------------------------------------------- *)
(* The K-PKE component scheme. The variable names are those of the           *)
(* pseudocode; ek, dk, c and the key halves are byte lists as in FIPS 203.   *)
(*                                                                           *)
(* kpke_keygen implements @[FIPS203, Algorithm 13, K-PKE.KeyGen],            *)
(* kpke_encrypt @[FIPS203, Algorithm 14, K-PKE.Encrypt] and                  *)
(* kpke_decrypt @[FIPS203, Algorithm 15, K-PKE.Decrypt].                     *)
(* ------------------------------------------------------------------------- *)

let kpke_keygen = new_definition
 `kpke_keygen ((k,eta1,eta2,du,dv):mlkem_params) (d:byte list) =
    let rho,sigma = mlkem_g (APPEND d [word k]) in
    let A = \i j. mlkem_ntt_inv
                   (mlkem_sample_ntt(APPEND rho [word j; word i])) in
    let s = \i. mlkem_cbd eta1 (mlkem_prf eta1 sigma (word i)) in
    let e = \i. mlkem_cbd eta1 (mlkem_prf eta1 sigma (word(k + i))) in
    let t = \i. ring_add mlkem_rq (mlkem_dot k (A i) s) (e i) in
    APPEND
     (mlkem_encode 12 (256 * k) (\n. mlkem_ntt (t(n DIV 256)) (n MOD 256)))
     rho,
    mlkem_encode 12 (256 * k) (\n. mlkem_ntt (s(n DIV 256)) (n MOD 256))`;;

let kpke_encrypt = new_definition
 `kpke_encrypt ((k,eta1,eta2,du,dv):mlkem_params)
               (ek:byte list) (m:byte list) (r:byte list) =
    let t = \i. mlkem_ntt_inv(\j. mlkem_decode 12 ek (256 * i + j)) in
    let rho = mlkem_slice (384 * k) 32 ek in
    let A = \i j. mlkem_ntt_inv
                   (mlkem_sample_ntt(APPEND rho [word j; word i])) in
    let y = \i. mlkem_cbd eta1 (mlkem_prf eta1 r (word i)) in
    let e1 = \i. mlkem_cbd eta2 (mlkem_prf eta2 r (word(k + i))) in
    let e2 = mlkem_cbd eta2 (mlkem_prf eta2 r (word(2 * k))) in
    let mu = mlkem_poly(\j. mlkem_decompress 1 (mlkem_decode 1 m j)) in
    let u = \i. ring_add mlkem_rq (mlkem_dot k (\j. A j i) y) (e1 i) in
    let v = ring_add mlkem_rq (ring_add mlkem_rq (mlkem_dot k t y) e2) mu in
    APPEND
     (mlkem_encode du (256 * k)
        (\n. mlkem_compress du (coeff (n MOD 256) (u(n DIV 256)))))
     (mlkem_encode dv 256 (\n. mlkem_compress dv (coeff n v)))`;;

let kpke_decrypt = new_definition
 `kpke_decrypt ((k,eta1,eta2,du,dv):mlkem_params)
               (dk:byte list) (c:byte list) =
    let c2 = mlkem_slice (32 * du * k) (32 * dv) c in
    let u = \i. mlkem_poly
                 (\j. mlkem_decompress du (mlkem_decode du c (256 * i + j))) in
    let v = mlkem_poly(\j. mlkem_decompress dv (mlkem_decode dv c2 j)) in
    let s = \i. mlkem_ntt_inv(\j. mlkem_decode 12 dk (256 * i + j)) in
    let w = ring_sub mlkem_rq v (mlkem_dot k s u) in
    mlkem_encode 1 256 (\j. mlkem_compress 1 (coeff j w))`;;

(* ------------------------------------------------------------------------- *)
(* The internal ML-KEM algorithms, which take their random inputs as         *)
(* arguments.                                                                *)
(*                                                                           *)
(* mlkem_keygen_internal implements @[FIPS203, Algorithm 16,                 *)
(* ML-KEM.KeyGen_internal], mlkem_encaps_internal @[FIPS203, Algorithm 17,   *)
(* ML-KEM.Encaps_internal] and mlkem_decaps_internal @[FIPS203, Algorithm    *)
(* 18, ML-KEM.Decaps_internal]. Key layouts as in the standard:              *)
(* dk = dk_pke || ek || H(ek) || z.                                          *)
(* ------------------------------------------------------------------------- *)

let mlkem_keygen_internal = new_definition
 `mlkem_keygen_internal ((k,eta1,eta2,du,dv):mlkem_params)
                        (d:byte list) (z:byte list) =
    let ek,dk = kpke_keygen (k,eta1,eta2,du,dv) d in
    ek,APPEND dk (APPEND ek (APPEND (mlkem_h ek) z))`;;

let mlkem_encaps_internal = new_definition
 `mlkem_encaps_internal ((k,eta1,eta2,du,dv):mlkem_params)
                        (ek:byte list) (m:byte list) =
    let kk,r = mlkem_g (APPEND m (mlkem_h ek)) in
    kk,kpke_encrypt (k,eta1,eta2,du,dv) ek m r`;;

let mlkem_decaps_internal = new_definition
 `mlkem_decaps_internal ((k,eta1,eta2,du,dv):mlkem_params)
                        (dk:byte list) (c:byte list) =
    let dk_pke = mlkem_slice 0 (384 * k) dk
    and ek_pke = mlkem_slice (384 * k) (384 * k + 32) dk
    and h = mlkem_slice (768 * k + 32) 32 dk
    and z = mlkem_slice (768 * k + 64) 32 dk in
    let m' = kpke_decrypt (k,eta1,eta2,du,dv) dk_pke c in
    let kk',r' = mlkem_g (APPEND m' h) in
    let kbar = mlkem_j (APPEND z c) in
    if kpke_encrypt (k,eta1,eta2,du,dv) ek_pke m' r' = c then kk' else kbar`;;

(* ------------------------------------------------------------------------- *)
(* Input checking.                                                           *)
(*                                                                           *)
(* mlkem_ek_check implements the type check and the modulus check of        *)
(* @[FIPS203, Section 7.2] on an encapsulation key; mlkem_decaps_check the   *)
(* type checks of the ciphertext and the decapsulation key and the hash      *)
(* check of @[FIPS203, Section 7.3]. The standard states these checks in     *)
(* prose, not as numbered algorithms, and requires that Encaps and Decaps    *)
(* are not run on inputs that fail them.                                     *)
(* ------------------------------------------------------------------------- *)

let mlkem_ek_check = new_definition
 `mlkem_ek_check ((k,eta1,eta2,du,dv):mlkem_params)
                 (ek:byte list) <=>
    LENGTH ek = 384 * k + 32 /\
    mlkem_encode 12 (256 * k) (mlkem_decode 12 ek) =
    mlkem_slice 0 (384 * k) ek`;;

let mlkem_decaps_check = new_definition
 `mlkem_decaps_check ((k,eta1,eta2,du,dv):mlkem_params)
                     (dk:byte list) (c:byte list) <=>
    LENGTH c = 32 * (du * k + dv) /\
    LENGTH dk = 768 * k + 96 /\
    mlkem_h (mlkem_slice (384 * k) (384 * k + 32) dk) =
    mlkem_slice (768 * k + 32) 32 dk`;;

(* ------------------------------------------------------------------------- *)
(* Checked variants of Encaps and Decaps.                                    *)
(*                                                                           *)
(* @[FIPS203, Algorithm 20, ML-KEM.Encaps] and @[FIPS203, Algorithm 21,      *)
(* ML-KEM.Decaps] are the internal algorithms above preceded by the input    *)
(* checks of @[FIPS203, Section 7.2] and @[FIPS203, Section 7.3]. The        *)
(* randomness m of Encaps is an argument here, so these are the derandomized *)
(* forms. Both return NONE when the check fails and SOME of the result of    *)
(* the internal algorithm otherwise:                                         *)
(*                                                                           *)
(*   mlkem_encaps_checked runs mlkem_ek_check (type and modulus check of     *)
(*   the encapsulation key).                                                 *)
(*                                                                           *)
(*   mlkem_decaps_checked runs mlkem_decaps_check (type checks of the        *)
(*   ciphertext and the decapsulation key, and the hash check of the         *)
(*   embedded encapsulation key).                                            *)
(*                                                                           *)
(* There is no checked variant of key generation: @[FIPS203, Algorithm 19,   *)
(* ML-KEM.KeyGen] draws d and z from a random bit generator and runs no      *)
(* input check, so mlkem_keygen_internal is the derandomized form.           *)
(* ------------------------------------------------------------------------- *)

let mlkem_encaps_checked = new_definition
 `mlkem_encaps_checked (p:mlkem_params) (ek:byte list) (m:byte list) =
    if mlkem_ek_check p ek then SOME(mlkem_encaps_internal p ek m) else NONE`;;

let mlkem_decaps_checked = new_definition
 `mlkem_decaps_checked (p:mlkem_params) (dk:byte list) (c:byte list) =
    if mlkem_decaps_check p dk c then SOME(mlkem_decaps_internal p dk c)
    else NONE`;;

(* Restore the default setting for anything loaded later.                    *)

type_invention_error := false;;
