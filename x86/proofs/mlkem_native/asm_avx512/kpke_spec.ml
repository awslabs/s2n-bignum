(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The algorithms of FIPS 203 for the proofs of the API functions of         *)
(* mlkem_native2 (x86/proofs/mlkem_native/asm/mlkem512.ml, mlkem768.ml and   *)
(* mlkem1024.ml): K-PKE key generation, encryption and decryption from the   *)
(* coefficients the kernels compute, given as congruences mod q with bounds, *)
(* for the three parameter sets. The lemmas are those of the proofs of the   *)
(* compiled C of mlkem-native, with the vectors also given as blocks of      *)
(* polynomials.                                                              *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mlkem_native_fips203.ml";;

(* ------------------------------------------------------------------------- *)
(* The algorithms of FIPS 203 used in the statements: lengths, and the       *)
(* internal ML-KEM algorithms (FIPS 203 Algorithms 16, 17 and 18) with the   *)
(* hash functions unfolded.                                                  *)
(* ------------------------------------------------------------------------- *)

let LENGTH_SHA3_256_STMT =
  `!m. LENGTH(sha3_256 m) = 32`;;

let LENGTH_SHA3_256 = assume_spec LENGTH_SHA3_256_STMT;;

let LENGTH_SHA3_512_STMT =
  `!m. LENGTH(sha3_512 m) = 64`;;

let LENGTH_SHA3_512 = assume_spec LENGTH_SHA3_512_STMT;;

let KPKE_KEYGEN_LENGTHS_STMT =
  `!k eta1 eta2 du dv d.
        LENGTH(FST(kpke_keygen (k,eta1,eta2,du,dv) d)) = 384 * k + 32 /\
        LENGTH(SND(kpke_keygen (k,eta1,eta2,du,dv) d)) = 384 * k`;;

let KPKE_KEYGEN_LENGTHS = assume_spec KPKE_KEYGEN_LENGTHS_STMT;;

let KPKE_ENCRYPT_LENGTH_STMT =
  `!k eta1 eta2 du dv ek m r.
        LENGTH(kpke_encrypt (k,eta1,eta2,du,dv) ek m r) = 32 * (du * k + dv)`;;

let KPKE_ENCRYPT_LENGTH = assume_spec KPKE_ENCRYPT_LENGTH_STMT;;

let KPKE_DECRYPT_LENGTH_STMT =
  `!k eta1 eta2 du dv dk c.
        LENGTH(kpke_decrypt (k,eta1,eta2,du,dv) dk c) = 32`;;

let KPKE_DECRYPT_LENGTH = assume_spec KPKE_DECRYPT_LENGTH_STMT;;

let MLKEM_SLICE_SLICE_STMT =
  `!a n b m (l:byte list).
        a + n <= m
        ==> mlkem_slice a n (mlkem_slice b m l) = mlkem_slice (b + a) n l`;;

let MLKEM_SLICE_SLICE = assume_spec MLKEM_SLICE_SLICE_STMT;;

let NUM_OF_BYTELIST_INJ_STMT =
  `!l1 l2:byte list.
        LENGTH l1 = LENGTH l2
        ==> (num_of_bytelist l1 = num_of_bytelist l2 <=> l1 = l2)`;;

let NUM_OF_BYTELIST_INJ = assume_spec NUM_OF_BYTELIST_INJ_STMT;;

let MLKEM_KEYGEN_PAIR_STMT =
  `!k eta1 eta2 du dv d z.
        mlkem_keygen_internal (k,eta1,eta2,du,dv) d z =
        FST(kpke_keygen (k,eta1,eta2,du,dv) d),
        APPEND (SND(kpke_keygen (k,eta1,eta2,du,dv) d))
         (APPEND (FST(kpke_keygen (k,eta1,eta2,du,dv) d))
           (APPEND (mlkem_h(FST(kpke_keygen (k,eta1,eta2,du,dv) d))) z))`;;

let MLKEM_KEYGEN_PAIR = assume_spec MLKEM_KEYGEN_PAIR_STMT;;

let MLKEM_ENCAPS_PAIR_STMT =
  `!k eta1 eta2 du dv ek m.
        mlkem_encaps_internal (k,eta1,eta2,du,dv) ek m =
        mlkem_slice 0 32 (sha3_512 (APPEND m (sha3_256 ek))),
        kpke_encrypt (k,eta1,eta2,du,dv) ek m
         (mlkem_slice 32 32 (sha3_512 (APPEND m (sha3_256 ek))))`;;

let MLKEM_ENCAPS_PAIR = assume_spec MLKEM_ENCAPS_PAIR_STMT;;

let MLKEM_DECAPS_ALT_STMT =
  `!k eta1 eta2 du dv dk c.
        mlkem_decaps_internal (k,eta1,eta2,du,dv) dk c =
        let m' = kpke_decrypt (k,eta1,eta2,du,dv)
                  (mlkem_slice 0 (384 * k) dk) c in
        let g = sha3_512 (APPEND m' (mlkem_slice (768 * k + 32) 32 dk)) in
        if kpke_encrypt (k,eta1,eta2,du,dv)
            (mlkem_slice (384 * k) (384 * k + 32) dk) m'
            (mlkem_slice 32 32 g) =
           c
        then mlkem_slice 0 32 g
        else list_of_seq
              (shake256 (APPEND (mlkem_slice (768 * k + 64) 32 dk) c))
                         32`;;

let MLKEM_DECAPS_ALT = assume_spec MLKEM_DECAPS_ALT_STMT;;

(* ------------------------------------------------------------------------- *)
(* K-PKE (FIPS 203 Algorithms 13, 14 and 15) from the coefficients computed  *)
(* by the kernels, for k = 2, 3 and 4, with the vectors as flat arrays of    *)
(* 256 * k coefficients.                                                     *)
(* ------------------------------------------------------------------------- *)

(*** Key generation for k = 2 (FIPS 203 Algorithm 13): the coefficients 2p
 *** and 2p + 1 of row r of t_hat = A_hat o s_hat + e_hat from the sums of
 *** the products accumulated by basemul, which carry the factor 169 = 2^-16
 *** mod q that tomont removes, and the key pair from all the coefficients
 ***)

let KPKE_KEYGEN_COEFF_EVEN_K2_STMT =
  `!(A:num->num->int) (Y:num->num->int) (YT:num->int) (SH:num->num->int)
    (t:int) (u:int) (e:int) (eh:int) p.
     (!j. j < 2 ==> (Y j (2 * p) == SH j (2 * p)) (mod &3329) /\
                    (Y j (2 * p + 1) == SH j (2 * p + 1)) (mod &3329) /\
                    (YT j == Y j (2 * p + 1) *
                             &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (t == &169 * ((A 1 (2 * p + 1) * YT 1 + A 1 (2 * p) * Y 1 (2 * p)) +
                   (A 0 (2 * p + 1) * YT 0 + A 0 (2 * p) * Y 0 (2 * p))))
     (mod &3329) /\
     (u == &65536 * t) (mod &3329) /\
     (e == eh) (mod &3329)
     ==> (u + e) rem &3329 =
         ring_add mlkem_zq
          (ring_sum mlkem_zq {j | j < 2}
             (\j. fips203_multiply_ntts (A j) (SH j) (2 * p)))
          eh`;;

let KPKE_KEYGEN_COEFF_EVEN_K2 = assume_spec KPKE_KEYGEN_COEFF_EVEN_K2_STMT;;

let KPKE_KEYGEN_COEFF_ODD_K2_STMT =
  `!(A:num->num->int) (Y:num->num->int) (SH:num->num->int)
    (t:int) (u:int) (e:int) (eh:int) p.
     (!j. j < 2 ==> (Y j (2 * p) == SH j (2 * p)) (mod &3329) /\
                    (Y j (2 * p + 1) == SH j (2 * p + 1)) (mod &3329)) /\
     (t == &169 *
           ((A 1 (2 * p + 1) * Y 1 (2 * p) + A 1 (2 * p) * Y 1 (2 * p + 1)) +
            (A 0 (2 * p + 1) * Y 0 (2 * p) + A 0 (2 * p) * Y 0 (2 * p + 1))))
     (mod &3329) /\
     (u == &65536 * t) (mod &3329) /\
     (e == eh) (mod &3329)
     ==> (u + e) rem &3329 =
         ring_add mlkem_zq
          (ring_sum mlkem_zq {j | j < 2}
             (\j. fips203_multiply_ntts (A j) (SH j) (2 * p + 1)))
          eh`;;

let KPKE_KEYGEN_COEFF_ODD_K2 = assume_spec KPKE_KEYGEN_COEFF_ODD_K2_STMT;;

let KPKE_KEYGEN_K2_RESULT_STMT =
  `!d rho sigma (sh:num->int16) (eh:num->int16) (mc:num->int16)
    (pt:num->int16) (pt2:num->int16) (tr:num->int16) (sr:num->int16).
     mlkem_g(APPEND d [word 2]) = rho,sigma /\
     (!i j n. i < 2 /\ j < 2 /\ n < 256
              ==> mlkem_sample_ntt (APPEND rho [word j; word i]) n < &3329) /\
     (!j i. j < 2 /\ i < 256
            ==> (ival(sh(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 3 (mlkem_prf 3 sigma (word j))) i)
                (mod &3329) /\
                abs(ival(sh(256 * j + i))) <= &23594) /\
     (!j i. j < 2 /\ i < 256
            ==> (ival(eh(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 3 (mlkem_prf 3 sigma (word(2 + j)))) i)
                (mod &3329) /\
                abs(ival(eh(256 * j + i))) <= &23594) /\
     (!j p. j < 2 /\ p < 128
            ==> (ival(mc(128 * j + p)) ==
                 ival(sh(256 * j + 2 * p + 1)) *
                 &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (!r p. r < 2 /\ p < 128
            ==> (ival(pt(256 * r + 2 * p)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p + 1) *
                   ival(mc(128 + p)) +
                   mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p) *
                   ival(sh(256 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p + 1) *
                   ival(mc p) +
                   mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p) *
                   ival(sh(2 * p))))) (mod &3329) /\
                (ival(pt(256 * r + 2 * p + 1)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p + 1) *
                   ival(sh(256 + 2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p) *
                   ival(sh(256 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p + 1) *
                   ival(sh(2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p) *
                   ival(sh(2 * p + 1))))) (mod &3329)) /\
     (!i. i < 512 ==> (ival(pt2 i) == &65536 * ival(pt i)) (mod &3329) /\
                      abs(ival(pt2 i)) <= &3328) /\
     (!i. i < 512 ==> ival(tr i) = ival(word_add (pt2 i) (eh i)) rem &3329) /\
     (!i. i < 512 ==> ival(sr i) = ival(sh i) rem &3329)
     ==> num_of_wordlist(MAP (word_zx:int16->12 word) (list_of_seq tr 512)) +
         2 EXP (8 * 768) * num_of_bytelist rho =
         num_of_bytelist(FST(kpke_keygen mlkem512 d)) /\
         num_of_wordlist(MAP (word_zx:int16->12 word) (list_of_seq sr 512)) =
         num_of_bytelist(SND(kpke_keygen mlkem512 d))`;;

let KPKE_KEYGEN_K2_RESULT = assume_spec KPKE_KEYGEN_K2_RESULT_STMT;;

(*** Key generation for k = 3 (FIPS 203 Algorithm 13): the coefficients 2p
 *** and 2p + 1 of row r of t_hat = A_hat o s_hat + e_hat from the sums of
 *** the products accumulated by basemul, which carry the factor 169 = 2^-16
 *** mod q that tomont removes, and the key pair from all the coefficients
 ***)

let KPKE_KEYGEN_COEFF_EVEN_K3_STMT =
  `!(A:num->num->int) (Y:num->num->int) (YT:num->int) (SH:num->num->int)
    (t:int) (u:int) (e:int) (eh:int) p.
     (!j. j < 3 ==> (Y j (2 * p) == SH j (2 * p)) (mod &3329) /\
                    (Y j (2 * p + 1) == SH j (2 * p + 1)) (mod &3329) /\
                    (YT j == Y j (2 * p + 1) *
                             &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (t == &169 * ((A 2 (2 * p + 1) * YT 2 + A 2 (2 * p) * Y 2 (2 * p)) +
                   (A 1 (2 * p + 1) * YT 1 + A 1 (2 * p) * Y 1 (2 * p)) +
                   (A 0 (2 * p + 1) * YT 0 + A 0 (2 * p) * Y 0 (2 * p))))
     (mod &3329) /\
     (u == &65536 * t) (mod &3329) /\
     (e == eh) (mod &3329)
     ==> (u + e) rem &3329 =
         ring_add mlkem_zq
          (ring_sum mlkem_zq {j | j < 3}
             (\j. fips203_multiply_ntts (A j) (SH j) (2 * p)))
          eh`;;

let KPKE_KEYGEN_COEFF_EVEN_K3 = assume_spec KPKE_KEYGEN_COEFF_EVEN_K3_STMT;;

let KPKE_KEYGEN_COEFF_ODD_K3_STMT =
  `!(A:num->num->int) (Y:num->num->int) (SH:num->num->int)
    (t:int) (u:int) (e:int) (eh:int) p.
     (!j. j < 3 ==> (Y j (2 * p) == SH j (2 * p)) (mod &3329) /\
                    (Y j (2 * p + 1) == SH j (2 * p + 1)) (mod &3329)) /\
     (t == &169 *
           ((A 2 (2 * p + 1) * Y 2 (2 * p) + A 2 (2 * p) * Y 2 (2 * p + 1)) +
            (A 1 (2 * p + 1) * Y 1 (2 * p) + A 1 (2 * p) * Y 1 (2 * p + 1)) +
            (A 0 (2 * p + 1) * Y 0 (2 * p) + A 0 (2 * p) * Y 0 (2 * p + 1))))
     (mod &3329) /\
     (u == &65536 * t) (mod &3329) /\
     (e == eh) (mod &3329)
     ==> (u + e) rem &3329 =
         ring_add mlkem_zq
          (ring_sum mlkem_zq {j | j < 3}
             (\j. fips203_multiply_ntts (A j) (SH j) (2 * p + 1)))
          eh`;;

let KPKE_KEYGEN_COEFF_ODD_K3 = assume_spec KPKE_KEYGEN_COEFF_ODD_K3_STMT;;

let KPKE_KEYGEN_K3_RESULT_STMT =
  `!d rho sigma (sh:num->int16) (eh:num->int16) (mc:num->int16)
    (pt:num->int16) (pt2:num->int16) (tr:num->int16) (sr:num->int16).
     mlkem_g(APPEND d [word 3]) = rho,sigma /\
     (!i j n. i < 3 /\ j < 3 /\ n < 256
              ==> mlkem_sample_ntt (APPEND rho [word j; word i]) n < &3329) /\
     (!j i. j < 3 /\ i < 256
            ==> (ival(sh(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word j))) i)
                (mod &3329) /\
                abs(ival(sh(256 * j + i))) <= &23594) /\
     (!j i. j < 3 /\ i < 256
            ==> (ival(eh(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word(3 + j)))) i)
                (mod &3329) /\
                abs(ival(eh(256 * j + i))) <= &23594) /\
     (!j p. j < 3 /\ p < 128
            ==> (ival(mc(128 * j + p)) ==
                 ival(sh(256 * j + 2 * p + 1)) *
                 &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (!r p. r < 3 /\ p < 128
            ==> (ival(pt(256 * r + 2 * p)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p + 1) *
                   ival(mc(256 + p)) +
                   mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p) *
                   ival(sh(512 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p + 1) *
                   ival(mc(128 + p)) +
                   mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p) *
                   ival(sh(256 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p + 1) *
                   ival(mc p) +
                   mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p) *
                   ival(sh(2 * p))))) (mod &3329) /\
                (ival(pt(256 * r + 2 * p + 1)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p + 1) *
                   ival(sh(512 + 2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p) *
                   ival(sh(512 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p + 1) *
                   ival(sh(256 + 2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p) *
                   ival(sh(256 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p + 1) *
                   ival(sh(2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p) *
                   ival(sh(2 * p + 1))))) (mod &3329)) /\
     (!i. i < 768 ==> (ival(pt2 i) == &65536 * ival(pt i)) (mod &3329) /\
                      abs(ival(pt2 i)) <= &3328) /\
     (!i. i < 768 ==> ival(tr i) = ival(word_add (pt2 i) (eh i)) rem &3329) /\
     (!i. i < 768 ==> ival(sr i) = ival(sh i) rem &3329)
     ==> num_of_wordlist(MAP (word_zx:int16->12 word) (list_of_seq tr 768)) +
         2 EXP (8 * 1152) * num_of_bytelist rho =
         num_of_bytelist(FST(kpke_keygen mlkem768 d)) /\
         num_of_wordlist(MAP (word_zx:int16->12 word) (list_of_seq sr 768)) =
         num_of_bytelist(SND(kpke_keygen mlkem768 d))`;;

let KPKE_KEYGEN_K3_RESULT = assume_spec KPKE_KEYGEN_K3_RESULT_STMT;;

(*** Key generation for k = 4 (FIPS 203 Algorithm 13): the coefficients 2p
 *** and 2p + 1 of row r of t_hat = A_hat o s_hat + e_hat from the sums of
 *** the products accumulated by basemul, which carry the factor 169 = 2^-16
 *** mod q that tomont removes, and the key pair from all the coefficients
 ***)

let KPKE_KEYGEN_COEFF_EVEN_K4_STMT =
  `!(A:num->num->int) (Y:num->num->int) (YT:num->int) (SH:num->num->int)
    (t:int) (u:int) (e:int) (eh:int) p.
     (!j. j < 4 ==> (Y j (2 * p) == SH j (2 * p)) (mod &3329) /\
                    (Y j (2 * p + 1) == SH j (2 * p + 1)) (mod &3329) /\
                    (YT j == Y j (2 * p + 1) *
                             &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (t == &169 * ((A 3 (2 * p + 1) * YT 3 + A 3 (2 * p) * Y 3 (2 * p)) +
                   (A 2 (2 * p + 1) * YT 2 + A 2 (2 * p) * Y 2 (2 * p)) +
                   (A 1 (2 * p + 1) * YT 1 + A 1 (2 * p) * Y 1 (2 * p)) +
                   (A 0 (2 * p + 1) * YT 0 + A 0 (2 * p) * Y 0 (2 * p))))
     (mod &3329) /\
     (u == &65536 * t) (mod &3329) /\
     (e == eh) (mod &3329)
     ==> (u + e) rem &3329 =
         ring_add mlkem_zq
          (ring_sum mlkem_zq {j | j < 4}
             (\j. fips203_multiply_ntts (A j) (SH j) (2 * p)))
          eh`;;

let KPKE_KEYGEN_COEFF_EVEN_K4 = assume_spec KPKE_KEYGEN_COEFF_EVEN_K4_STMT;;

let KPKE_KEYGEN_COEFF_ODD_K4_STMT =
  `!(A:num->num->int) (Y:num->num->int) (SH:num->num->int)
    (t:int) (u:int) (e:int) (eh:int) p.
     (!j. j < 4 ==> (Y j (2 * p) == SH j (2 * p)) (mod &3329) /\
                    (Y j (2 * p + 1) == SH j (2 * p + 1)) (mod &3329)) /\
     (t == &169 *
           ((A 3 (2 * p + 1) * Y 3 (2 * p) + A 3 (2 * p) * Y 3 (2 * p + 1)) +
            (A 2 (2 * p + 1) * Y 2 (2 * p) + A 2 (2 * p) * Y 2 (2 * p + 1)) +
            (A 1 (2 * p + 1) * Y 1 (2 * p) + A 1 (2 * p) * Y 1 (2 * p + 1)) +
            (A 0 (2 * p + 1) * Y 0 (2 * p) + A 0 (2 * p) * Y 0 (2 * p + 1))))
     (mod &3329) /\
     (u == &65536 * t) (mod &3329) /\
     (e == eh) (mod &3329)
     ==> (u + e) rem &3329 =
         ring_add mlkem_zq
          (ring_sum mlkem_zq {j | j < 4}
             (\j. fips203_multiply_ntts (A j) (SH j) (2 * p + 1)))
          eh`;;

let KPKE_KEYGEN_COEFF_ODD_K4 = assume_spec KPKE_KEYGEN_COEFF_ODD_K4_STMT;;

let KPKE_KEYGEN_K4_RESULT_STMT =
  `!d rho sigma (sh:num->int16) (eh:num->int16) (mc:num->int16)
    (pt:num->int16) (pt2:num->int16) (tr:num->int16) (sr:num->int16).
     mlkem_g(APPEND d [word 4]) = rho,sigma /\
     (!i j n. i < 4 /\ j < 4 /\ n < 256
              ==> mlkem_sample_ntt (APPEND rho [word j; word i]) n < &3329) /\
     (!j i. j < 4 /\ i < 256
            ==> (ival(sh(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word j))) i)
                (mod &3329) /\
                abs(ival(sh(256 * j + i))) <= &23594) /\
     (!j i. j < 4 /\ i < 256
            ==> (ival(eh(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word(4 + j)))) i)
                (mod &3329) /\
                abs(ival(eh(256 * j + i))) <= &23594) /\
     (!j p. j < 4 /\ p < 128
            ==> (ival(mc(128 * j + p)) ==
                 ival(sh(256 * j + 2 * p + 1)) *
                 &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (!r p. r < 4 /\ p < 128
            ==> (ival(pt(256 * r + 2 * p)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND rho [word 3; word r]) (2 * p + 1) *
                   ival(mc(384 + p)) +
                   mlkem_sample_ntt (APPEND rho [word 3; word r]) (2 * p) *
                   ival(sh(768 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p + 1) *
                   ival(mc(256 + p)) +
                   mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p) *
                   ival(sh(512 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p + 1) *
                   ival(mc(128 + p)) +
                   mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p) *
                   ival(sh(256 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p + 1) *
                   ival(mc p) +
                   mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p) *
                   ival(sh(2 * p))))) (mod &3329) /\
                (ival(pt(256 * r + 2 * p + 1)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND rho [word 3; word r]) (2 * p + 1) *
                   ival(sh(768 + 2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 3; word r]) (2 * p) *
                   ival(sh(768 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p + 1) *
                   ival(sh(512 + 2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p) *
                   ival(sh(512 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p + 1) *
                   ival(sh(256 + 2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p) *
                   ival(sh(256 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p + 1) *
                   ival(sh(2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p) *
                   ival(sh(2 * p + 1))))) (mod &3329)) /\
     (!i. i < 1024 ==> (ival(pt2 i) == &65536 * ival(pt i)) (mod &3329) /\
                      abs(ival(pt2 i)) <= &3328) /\
     (!i. i < 1024 ==> ival(tr i) = ival(word_add (pt2 i) (eh i)) rem &3329) /\
     (!i. i < 1024 ==> ival(sr i) = ival(sh i) rem &3329)
     ==> num_of_wordlist(MAP (word_zx:int16->12 word) (list_of_seq tr 1024)) +
         2 EXP (8 * 1536) * num_of_bytelist rho =
         num_of_bytelist(FST(kpke_keygen mlkem1024 d)) /\
         num_of_wordlist(MAP (word_zx:int16->12 word) (list_of_seq sr 1024)) =
         num_of_bytelist(SND(kpke_keygen mlkem1024 d))`;;

let KPKE_KEYGEN_K4_RESULT = assume_spec KPKE_KEYGEN_K4_RESULT_STMT;;

(*** Encryption for k = 2 (FIPS 203 Algorithm 14): the ciphertext from
 *** t_hat decoded from ek, y_hat and its mulcache, e1, e2 and the message
 *** mu, the products of A_hat^T and of t_hat^T with y_hat, their inverse
 *** NTTs, the sums with the noise and the reductions before compression
 ***)

let KPKE_ENCRYPT_K2_RESULT_STMT =
  `!ek m r (TT:num->int16) (YH:num->int16) (MC:num->int16) (E1:num->int16)
    (E2:num->int16) (MU:num->int16) (U0:num->int16) (V0:num->int16)
    (U1:num->int16) (V1:num->int16) (U3:num->int16) (V4:num->int16).
     (!i j n. i < 2 /\ j < 2 /\ n < 256
              ==> mlkem_sample_ntt
                   (APPEND (mlkem_slice 768 32 ek) [word j; word i]) n
                  < &3329) /\
     (!i. i < 512
          ==> TT i = word((num_of_bytelist ek DIV 2 EXP (12 * i)) MOD
                          2 EXP 12)) /\
     (!j i. j < 2 /\ i < 256
            ==> (ival(YH(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 3 (mlkem_prf 3 r (word j))) i)
                (mod &3329) /\
                abs(ival(YH(256 * j + i))) <= &23594) /\
     (!j p. j < 2 /\ p < 128
            ==> (ival(MC(128 * j + p)) ==
                 ival(YH(256 * j + 2 * p + 1)) *
                 &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (!j i. j < 2 /\ i < 256
            ==> (ival(E1(256 * j + i)) ==
                 coeff i (mlkem_cbd 2 (mlkem_prf 2 r (word(2 + j)))))
                (mod &3329) /\
                abs(ival(E1(256 * j + i))) <= &2) /\
     (!i. i < 256
          ==> (ival(E2 i) == coeff i (mlkem_cbd 2 (mlkem_prf 2 r (word 4))))
              (mod &3329) /\
              abs(ival(E2 i)) <= &2) /\
     (!i. i < 256
          ==> MU i = word((3329 * (num_of_bytelist m DIV 2 EXP i) MOD 2 + 1)
                          DIV 2)) /\
     (!q p. q < 2 /\ p < 128
            ==> (ival(U0(256 * q + 2 * p)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND (mlkem_slice 768 32 ek)
                                       [word q; word 1]) (2 * p + 1) *
                   ival(MC(128 + p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 768 32 ek)
                                       [word q; word 1]) (2 * p) *
                   ival(YH(256 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 768 32 ek)
                                       [word q; word 0]) (2 * p + 1) *
                   ival(MC p) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 768 32 ek)
                                       [word q; word 0]) (2 * p) *
                   ival(YH(2 * p))))) (mod &3329) /\
                (ival(U0(256 * q + 2 * p + 1)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND (mlkem_slice 768 32 ek)
                                       [word q; word 1]) (2 * p + 1) *
                   ival(YH(256 + 2 * p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 768 32 ek)
                                       [word q; word 1]) (2 * p) *
                   ival(YH(256 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 768 32 ek)
                                       [word q; word 0]) (2 * p + 1) *
                   ival(YH(2 * p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 768 32 ek)
                                       [word q; word 0]) (2 * p) *
                   ival(YH(2 * p + 1))))) (mod &3329)) /\
     (!p. p < 128
          ==> (ival(V0(2 * p)) ==
               &169 *
               ((ival(TT(256 + 2 * p + 1)) * ival(MC(128 + p)) +
                 ival(TT(256 + 2 * p)) * ival(YH(256 + 2 * p))) +
                (ival(TT(2 * p + 1)) * ival(MC p) +
                 ival(TT(2 * p)) * ival(YH(2 * p))))) (mod &3329) /\
              (ival(V0(2 * p + 1)) ==
               &169 *
               ((ival(TT(256 + 2 * p + 1)) * ival(YH(256 + 2 * p)) +
                 ival(TT(256 + 2 * p)) * ival(YH(256 + 2 * p + 1))) +
                (ival(TT(2 * p + 1)) * ival(YH(2 * p)) +
                 ival(TT(2 * p)) * ival(YH(2 * p + 1))))) (mod &3329)) /\
     (!j i. j < 2 /\ i < 256
            ==> (ival(U1(256 * j + i)) ==
                 inverse_ntt (\n. ival(U0(256 * j + n))) i) (mod &3329) /\
                abs(ival(U1(256 * j + i))) <= &26631) /\
     (!i. i < 256
          ==> (ival(V1 i) == inverse_ntt (\n. ival(V0 n)) i) (mod &3329) /\
              abs(ival(V1 i)) <= &26631) /\
     (!i. i < 512 ==> ival(U3 i) = ival(word_add (U1 i) (E1 i)) rem &3329) /\
     (!i. i < 256
          ==> ival(V4 i) =
              ival(word_add (word_add (V1 i) (E2 i)) (MU i)) rem &3329)
     ==> nsum {i | i < 512}
              (\i. ((2048 * val(U3 i) + 3329) DIV 6658) MOD 1024 *
                   2 EXP (10 * i)) +
         2 EXP (8 * 640) *
         nsum {i | i < 256}
              (\i. ((32 * val(V4 i) + 3329) DIV 6658) MOD 16 * 2 EXP (4 * i)) =
         num_of_bytelist(kpke_encrypt mlkem512 ek m r)`;;

let KPKE_ENCRYPT_K2_RESULT = assume_spec KPKE_ENCRYPT_K2_RESULT_STMT;;

(*** Decryption for k = 2 (FIPS 203 Algorithm 15): the message from u and
 *** v decompressed from the ciphertext, s_hat decoded from dk, u_hat and
 *** its mulcache, the product of s_hat^T and u_hat, its inverse NTT and
 *** the reduced difference v - w before compression
 ***)

let KPKE_DECRYPT_K2_RESULT_STMT =
  `!dk ct (UD:num->int16) (VD:num->int16) (SV:num->int16) (UH:num->int16)
    (MC:num->int16) (WP:num->int16) (WI:num->int16) (VR:num->int16).
     (!i. i < 512
          ==> UD i =
              word((3329 * (num_of_bytelist ct DIV 2 EXP (10 * i)) MOD
                    2 EXP 10 + 512) DIV 1024)) /\
     (!i. i < 256
          ==> VD i =
              word((3329 * (num_of_bytelist(mlkem_slice 640 128 ct) DIV
                            2 EXP (4 * i)) MOD 2 EXP 4 + 8) DIV 16)) /\
     (!i. i < 512
          ==> SV i = word((num_of_bytelist dk DIV 2 EXP (12 * i)) MOD
                          2 EXP 12)) /\
     (!j i. j < 2 /\ i < 256
            ==> (ival(UH(256 * j + i)) ==
                 forward_ntt (\n. ival(UD(256 * j + n))) i) (mod &3329) /\
                abs(ival(UH(256 * j + i))) <= &23594) /\
     (!j p. j < 2 /\ p < 128
            ==> (ival(MC(128 * j + p)) ==
                 ival(UH(256 * j + 2 * p + 1)) *
                 &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (!p. p < 128
          ==> (ival(WP(2 * p)) ==
               &169 *
               ((ival(SV(256 + 2 * p + 1)) * ival(MC(128 + p)) +
                 ival(SV(256 + 2 * p)) * ival(UH(256 + 2 * p))) +
                (ival(SV(2 * p + 1)) * ival(MC p) +
                 ival(SV(2 * p)) * ival(UH(2 * p))))) (mod &3329) /\
              (ival(WP(2 * p + 1)) ==
               &169 *
               ((ival(SV(256 + 2 * p + 1)) * ival(UH(256 + 2 * p)) +
                 ival(SV(256 + 2 * p)) * ival(UH(256 + 2 * p + 1))) +
                (ival(SV(2 * p + 1)) * ival(UH(2 * p)) +
                 ival(SV(2 * p)) * ival(UH(2 * p + 1))))) (mod &3329)) /\
     (!i. i < 256
          ==> (ival(WI i) == inverse_ntt (\n. ival(WP n)) i) (mod &3329) /\
              abs(ival(WI i)) <= &26631) /\
     (!i. i < 256 ==> ival(VR i) = ival(word_sub (VD i) (WI i)) rem &3329)
     ==> nsum {i | i < 256}
              (\i. ((4 * val(VR i) + 3329) DIV 6658) MOD 2 * 2 EXP i) =
         num_of_bytelist(kpke_decrypt mlkem512 dk ct)`;;

let KPKE_DECRYPT_K2_RESULT = assume_spec KPKE_DECRYPT_K2_RESULT_STMT;;

(*** The modulus check of an encapsulation key for k = 2 (FIPS 203
 *** section 7.2) as the bound of its 12-bit fields
 ***)

let MLKEM_EK_CHECK_512_STMT =
  `!ek. LENGTH ek = 800
        ==> (mlkem_ek_check mlkem512 ek <=>
             !i. i < 512
                 ==> (num_of_bytelist ek DIV 2 EXP (12 * i)) MOD 2 EXP 12
                     < 3329)`;;

let MLKEM_EK_CHECK_512 = assume_spec MLKEM_EK_CHECK_512_STMT;;

(*** Encryption for k = 3 (FIPS 203 Algorithm 14): the ciphertext from
 *** t_hat decoded from ek, y_hat and its mulcache, e1, e2 and the message
 *** mu, the products of A_hat^T and of t_hat^T with y_hat, their inverse
 *** NTTs, the sums with the noise and the reductions before compression
 ***)

let KPKE_ENCRYPT_K3_RESULT_STMT =
  `!ek m r (TT:num->int16) (YH:num->int16) (MC:num->int16) (E1:num->int16)
    (E2:num->int16) (MU:num->int16) (U0:num->int16) (V0:num->int16)
    (U1:num->int16) (V1:num->int16) (U3:num->int16) (V4:num->int16).
     (!i j n. i < 3 /\ j < 3 /\ n < 256
              ==> mlkem_sample_ntt
                   (APPEND (mlkem_slice 1152 32 ek) [word j; word i]) n
                  < &3329) /\
     (!i. i < 768
          ==> TT i = word((num_of_bytelist ek DIV 2 EXP (12 * i)) MOD
                          2 EXP 12)) /\
     (!j i. j < 3 /\ i < 256
            ==> (ival(YH(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 r (word j))) i)
                (mod &3329) /\
                abs(ival(YH(256 * j + i))) <= &23594) /\
     (!j p. j < 3 /\ p < 128
            ==> (ival(MC(128 * j + p)) ==
                 ival(YH(256 * j + 2 * p + 1)) *
                 &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (!j i. j < 3 /\ i < 256
            ==> (ival(E1(256 * j + i)) ==
                 coeff i (mlkem_cbd 2 (mlkem_prf 2 r (word(3 + j)))))
                (mod &3329) /\
                abs(ival(E1(256 * j + i))) <= &2) /\
     (!i. i < 256
          ==> (ival(E2 i) == coeff i (mlkem_cbd 2 (mlkem_prf 2 r (word 6))))
              (mod &3329) /\
              abs(ival(E2 i)) <= &2) /\
     (!i. i < 256
          ==> MU i = word((3329 * (num_of_bytelist m DIV 2 EXP i) MOD 2 + 1)
                          DIV 2)) /\
     (!q p. q < 3 /\ p < 128
            ==> (ival(U0(256 * q + 2 * p)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 2]) (2 * p + 1) *
                   ival(MC(256 + p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 2]) (2 * p) *
                   ival(YH(512 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 1]) (2 * p + 1) *
                   ival(MC(128 + p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 1]) (2 * p) *
                   ival(YH(256 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 0]) (2 * p + 1) *
                   ival(MC p) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 0]) (2 * p) *
                   ival(YH(2 * p))))) (mod &3329) /\
                (ival(U0(256 * q + 2 * p + 1)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 2]) (2 * p + 1) *
                   ival(YH(512 + 2 * p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 2]) (2 * p) *
                   ival(YH(512 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 1]) (2 * p + 1) *
                   ival(YH(256 + 2 * p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 1]) (2 * p) *
                   ival(YH(256 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 0]) (2 * p + 1) *
                   ival(YH(2 * p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 0]) (2 * p) *
                   ival(YH(2 * p + 1))))) (mod &3329)) /\
     (!p. p < 128
          ==> (ival(V0(2 * p)) ==
               &169 *
               ((ival(TT(512 + 2 * p + 1)) * ival(MC(256 + p)) +
                 ival(TT(512 + 2 * p)) * ival(YH(512 + 2 * p))) +
                (ival(TT(256 + 2 * p + 1)) * ival(MC(128 + p)) +
                 ival(TT(256 + 2 * p)) * ival(YH(256 + 2 * p))) +
                (ival(TT(2 * p + 1)) * ival(MC p) +
                 ival(TT(2 * p)) * ival(YH(2 * p))))) (mod &3329) /\
              (ival(V0(2 * p + 1)) ==
               &169 *
               ((ival(TT(512 + 2 * p + 1)) * ival(YH(512 + 2 * p)) +
                 ival(TT(512 + 2 * p)) * ival(YH(512 + 2 * p + 1))) +
                (ival(TT(256 + 2 * p + 1)) * ival(YH(256 + 2 * p)) +
                 ival(TT(256 + 2 * p)) * ival(YH(256 + 2 * p + 1))) +
                (ival(TT(2 * p + 1)) * ival(YH(2 * p)) +
                 ival(TT(2 * p)) * ival(YH(2 * p + 1))))) (mod &3329)) /\
     (!j i. j < 3 /\ i < 256
            ==> (ival(U1(256 * j + i)) ==
                 inverse_ntt (\n. ival(U0(256 * j + n))) i) (mod &3329) /\
                abs(ival(U1(256 * j + i))) <= &26631) /\
     (!i. i < 256
          ==> (ival(V1 i) == inverse_ntt (\n. ival(V0 n)) i) (mod &3329) /\
              abs(ival(V1 i)) <= &26631) /\
     (!i. i < 768 ==> ival(U3 i) = ival(word_add (U1 i) (E1 i)) rem &3329) /\
     (!i. i < 256
          ==> ival(V4 i) =
              ival(word_add (word_add (V1 i) (E2 i)) (MU i)) rem &3329)
     ==> nsum {i | i < 768}
              (\i. ((2048 * val(U3 i) + 3329) DIV 6658) MOD 1024 *
                   2 EXP (10 * i)) +
         2 EXP (8 * 960) *
         nsum {i | i < 256}
              (\i. ((32 * val(V4 i) + 3329) DIV 6658) MOD 16 * 2 EXP (4 * i)) =
         num_of_bytelist(kpke_encrypt mlkem768 ek m r)`;;

let KPKE_ENCRYPT_K3_RESULT = assume_spec KPKE_ENCRYPT_K3_RESULT_STMT;;

(*** Decryption for k = 3 (FIPS 203 Algorithm 15): the message from u and
 *** v decompressed from the ciphertext, s_hat decoded from dk, u_hat and
 *** its mulcache, the product of s_hat^T and u_hat, its inverse NTT and
 *** the reduced difference v - w before compression
 ***)

let KPKE_DECRYPT_K3_RESULT_STMT =
  `!dk ct (UD:num->int16) (VD:num->int16) (SV:num->int16) (UH:num->int16)
    (MC:num->int16) (WP:num->int16) (WI:num->int16) (VR:num->int16).
     (!i. i < 768
          ==> UD i =
              word((3329 * (num_of_bytelist ct DIV 2 EXP (10 * i)) MOD
                    2 EXP 10 + 512) DIV 1024)) /\
     (!i. i < 256
          ==> VD i =
              word((3329 * (num_of_bytelist(mlkem_slice 960 128 ct) DIV
                            2 EXP (4 * i)) MOD 2 EXP 4 + 8) DIV 16)) /\
     (!i. i < 768
          ==> SV i = word((num_of_bytelist dk DIV 2 EXP (12 * i)) MOD
                          2 EXP 12)) /\
     (!j i. j < 3 /\ i < 256
            ==> (ival(UH(256 * j + i)) ==
                 forward_ntt (\n. ival(UD(256 * j + n))) i) (mod &3329) /\
                abs(ival(UH(256 * j + i))) <= &23594) /\
     (!j p. j < 3 /\ p < 128
            ==> (ival(MC(128 * j + p)) ==
                 ival(UH(256 * j + 2 * p + 1)) *
                 &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (!p. p < 128
          ==> (ival(WP(2 * p)) ==
               &169 *
               ((ival(SV(512 + 2 * p + 1)) * ival(MC(256 + p)) +
                 ival(SV(512 + 2 * p)) * ival(UH(512 + 2 * p))) +
                (ival(SV(256 + 2 * p + 1)) * ival(MC(128 + p)) +
                 ival(SV(256 + 2 * p)) * ival(UH(256 + 2 * p))) +
                (ival(SV(2 * p + 1)) * ival(MC p) +
                 ival(SV(2 * p)) * ival(UH(2 * p))))) (mod &3329) /\
              (ival(WP(2 * p + 1)) ==
               &169 *
               ((ival(SV(512 + 2 * p + 1)) * ival(UH(512 + 2 * p)) +
                 ival(SV(512 + 2 * p)) * ival(UH(512 + 2 * p + 1))) +
                (ival(SV(256 + 2 * p + 1)) * ival(UH(256 + 2 * p)) +
                 ival(SV(256 + 2 * p)) * ival(UH(256 + 2 * p + 1))) +
                (ival(SV(2 * p + 1)) * ival(UH(2 * p)) +
                 ival(SV(2 * p)) * ival(UH(2 * p + 1))))) (mod &3329)) /\
     (!i. i < 256
          ==> (ival(WI i) == inverse_ntt (\n. ival(WP n)) i) (mod &3329) /\
              abs(ival(WI i)) <= &26631) /\
     (!i. i < 256 ==> ival(VR i) = ival(word_sub (VD i) (WI i)) rem &3329)
     ==> nsum {i | i < 256}
              (\i. ((4 * val(VR i) + 3329) DIV 6658) MOD 2 * 2 EXP i) =
         num_of_bytelist(kpke_decrypt mlkem768 dk ct)`;;

let KPKE_DECRYPT_K3_RESULT = assume_spec KPKE_DECRYPT_K3_RESULT_STMT;;

(*** The modulus check of an encapsulation key for k = 3 (FIPS 203
 *** section 7.2) as the bound of its 12-bit fields
 ***)

let MLKEM_EK_CHECK_768_STMT =
  `!ek. LENGTH ek = 1184
        ==> (mlkem_ek_check mlkem768 ek <=>
             !i. i < 768
                 ==> (num_of_bytelist ek DIV 2 EXP (12 * i)) MOD 2 EXP 12
                     < 3329)`;;

let MLKEM_EK_CHECK_768 = assume_spec MLKEM_EK_CHECK_768_STMT;;

(*** Encryption for k = 4 (FIPS 203 Algorithm 14): the ciphertext from
 *** t_hat decoded from ek, y_hat and its mulcache, e1, e2 and the message
 *** mu, the products of A_hat^T and of t_hat^T with y_hat, their inverse
 *** NTTs, the sums with the noise and the reductions before compression
 ***)

let KPKE_ENCRYPT_K4_RESULT_STMT =
  `!ek m r (TT:num->int16) (YH:num->int16) (MC:num->int16) (E1:num->int16)
    (E2:num->int16) (MU:num->int16) (U0:num->int16) (V0:num->int16)
    (U1:num->int16) (V1:num->int16) (U3:num->int16) (V4:num->int16).
     (!i j n. i < 4 /\ j < 4 /\ n < 256
              ==> mlkem_sample_ntt
                   (APPEND (mlkem_slice 1536 32 ek) [word j; word i]) n
                  < &3329) /\
     (!i. i < 1024
          ==> TT i = word((num_of_bytelist ek DIV 2 EXP (12 * i)) MOD
                          2 EXP 12)) /\
     (!j i. j < 4 /\ i < 256
            ==> (ival(YH(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 r (word j))) i)
                (mod &3329) /\
                abs(ival(YH(256 * j + i))) <= &23594) /\
     (!j p. j < 4 /\ p < 128
            ==> (ival(MC(128 * j + p)) ==
                 ival(YH(256 * j + 2 * p + 1)) *
                 &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (!j i. j < 4 /\ i < 256
            ==> (ival(E1(256 * j + i)) ==
                 coeff i (mlkem_cbd 2 (mlkem_prf 2 r (word(4 + j)))))
                (mod &3329) /\
                abs(ival(E1(256 * j + i))) <= &2) /\
     (!i. i < 256
          ==> (ival(E2 i) == coeff i (mlkem_cbd 2 (mlkem_prf 2 r (word 8))))
              (mod &3329) /\
              abs(ival(E2 i)) <= &2) /\
     (!i. i < 256
          ==> MU i = word((3329 * (num_of_bytelist m DIV 2 EXP i) MOD 2 + 1)
                          DIV 2)) /\
     (!q p. q < 4 /\ p < 128
            ==> (ival(U0(256 * q + 2 * p)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 3]) (2 * p + 1) *
                   ival(MC(384 + p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 3]) (2 * p) *
                   ival(YH(768 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 2]) (2 * p + 1) *
                   ival(MC(256 + p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 2]) (2 * p) *
                   ival(YH(512 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 1]) (2 * p + 1) *
                   ival(MC(128 + p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 1]) (2 * p) *
                   ival(YH(256 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 0]) (2 * p + 1) *
                   ival(MC p) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 0]) (2 * p) *
                   ival(YH(2 * p))))) (mod &3329) /\
                (ival(U0(256 * q + 2 * p + 1)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 3]) (2 * p + 1) *
                   ival(YH(768 + 2 * p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 3]) (2 * p) *
                   ival(YH(768 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 2]) (2 * p + 1) *
                   ival(YH(512 + 2 * p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 2]) (2 * p) *
                   ival(YH(512 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 1]) (2 * p + 1) *
                   ival(YH(256 + 2 * p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 1]) (2 * p) *
                   ival(YH(256 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 0]) (2 * p + 1) *
                   ival(YH(2 * p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 0]) (2 * p) *
                   ival(YH(2 * p + 1))))) (mod &3329)) /\
     (!p. p < 128
          ==> (ival(V0(2 * p)) ==
               &169 *
               ((ival(TT(768 + 2 * p + 1)) * ival(MC(384 + p)) +
                 ival(TT(768 + 2 * p)) * ival(YH(768 + 2 * p))) +
                (ival(TT(512 + 2 * p + 1)) * ival(MC(256 + p)) +
                 ival(TT(512 + 2 * p)) * ival(YH(512 + 2 * p))) +
                (ival(TT(256 + 2 * p + 1)) * ival(MC(128 + p)) +
                 ival(TT(256 + 2 * p)) * ival(YH(256 + 2 * p))) +
                (ival(TT(2 * p + 1)) * ival(MC p) +
                 ival(TT(2 * p)) * ival(YH(2 * p))))) (mod &3329) /\
              (ival(V0(2 * p + 1)) ==
               &169 *
               ((ival(TT(768 + 2 * p + 1)) * ival(YH(768 + 2 * p)) +
                 ival(TT(768 + 2 * p)) * ival(YH(768 + 2 * p + 1))) +
                (ival(TT(512 + 2 * p + 1)) * ival(YH(512 + 2 * p)) +
                 ival(TT(512 + 2 * p)) * ival(YH(512 + 2 * p + 1))) +
                (ival(TT(256 + 2 * p + 1)) * ival(YH(256 + 2 * p)) +
                 ival(TT(256 + 2 * p)) * ival(YH(256 + 2 * p + 1))) +
                (ival(TT(2 * p + 1)) * ival(YH(2 * p)) +
                 ival(TT(2 * p)) * ival(YH(2 * p + 1))))) (mod &3329)) /\
     (!j i. j < 4 /\ i < 256
            ==> (ival(U1(256 * j + i)) ==
                 inverse_ntt (\n. ival(U0(256 * j + n))) i) (mod &3329) /\
                abs(ival(U1(256 * j + i))) <= &26631) /\
     (!i. i < 256
          ==> (ival(V1 i) == inverse_ntt (\n. ival(V0 n)) i) (mod &3329) /\
              abs(ival(V1 i)) <= &26631) /\
     (!i. i < 1024
          ==> ival(U3 i) = ival(word_add (U1 i) (E1 i)) rem &3329) /\
     (!i. i < 256
          ==> ival(V4 i) =
              ival(word_add (word_add (V1 i) (E2 i)) (MU i)) rem &3329)
     ==> nsum {i | i < 1024}
              (\i. ((4096 * val(U3 i) + 3329) DIV 6658) MOD 2048 *
                   2 EXP (11 * i)) +
         2 EXP (8 * 1408) *
         nsum {i | i < 256}
              (\i. ((64 * val(V4 i) + 3329) DIV 6658) MOD 32 * 2 EXP (5 * i)) =
         num_of_bytelist(kpke_encrypt mlkem1024 ek m r)`;;

let KPKE_ENCRYPT_K4_RESULT = assume_spec KPKE_ENCRYPT_K4_RESULT_STMT;;

(*** Decryption for k = 4 (FIPS 203 Algorithm 15): the message from u and
 *** v decompressed from the ciphertext, s_hat decoded from dk, u_hat and
 *** its mulcache, the product of s_hat^T and u_hat, its inverse NTT and
 *** the reduced difference v - w before compression
 ***)

let KPKE_DECRYPT_K4_RESULT_STMT =
  `!dk ct (UD:num->int16) (VD:num->int16) (SV:num->int16) (UH:num->int16)
    (MC:num->int16) (WP:num->int16) (WI:num->int16) (VR:num->int16).
     (!i. i < 1024
          ==> UD i =
              word((3329 * (num_of_bytelist ct DIV 2 EXP (11 * i)) MOD
                    2 EXP 11 + 1024) DIV 2048)) /\
     (!i. i < 256
          ==> VD i =
              word((3329 * (num_of_bytelist(mlkem_slice 1408 160 ct) DIV
                            2 EXP (5 * i)) MOD 2 EXP 5 + 16) DIV 32)) /\
     (!i. i < 1024
          ==> SV i = word((num_of_bytelist dk DIV 2 EXP (12 * i)) MOD
                          2 EXP 12)) /\
     (!j i. j < 4 /\ i < 256
            ==> (ival(UH(256 * j + i)) ==
                 forward_ntt (\n. ival(UD(256 * j + n))) i) (mod &3329) /\
                abs(ival(UH(256 * j + i))) <= &23594) /\
     (!j p. j < 4 /\ p < 128
            ==> (ival(MC(128 * j + p)) ==
                 ival(UH(256 * j + 2 * p + 1)) *
                 &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (!p. p < 128
          ==> (ival(WP(2 * p)) ==
               &169 *
               ((ival(SV(768 + 2 * p + 1)) * ival(MC(384 + p)) +
                 ival(SV(768 + 2 * p)) * ival(UH(768 + 2 * p))) +
                (ival(SV(512 + 2 * p + 1)) * ival(MC(256 + p)) +
                 ival(SV(512 + 2 * p)) * ival(UH(512 + 2 * p))) +
                (ival(SV(256 + 2 * p + 1)) * ival(MC(128 + p)) +
                 ival(SV(256 + 2 * p)) * ival(UH(256 + 2 * p))) +
                (ival(SV(2 * p + 1)) * ival(MC p) +
                 ival(SV(2 * p)) * ival(UH(2 * p))))) (mod &3329) /\
              (ival(WP(2 * p + 1)) ==
               &169 *
               ((ival(SV(768 + 2 * p + 1)) * ival(UH(768 + 2 * p)) +
                 ival(SV(768 + 2 * p)) * ival(UH(768 + 2 * p + 1))) +
                (ival(SV(512 + 2 * p + 1)) * ival(UH(512 + 2 * p)) +
                 ival(SV(512 + 2 * p)) * ival(UH(512 + 2 * p + 1))) +
                (ival(SV(256 + 2 * p + 1)) * ival(UH(256 + 2 * p)) +
                 ival(SV(256 + 2 * p)) * ival(UH(256 + 2 * p + 1))) +
                (ival(SV(2 * p + 1)) * ival(UH(2 * p)) +
                 ival(SV(2 * p)) * ival(UH(2 * p + 1))))) (mod &3329)) /\
     (!i. i < 256
          ==> (ival(WI i) == inverse_ntt (\n. ival(WP n)) i) (mod &3329) /\
              abs(ival(WI i)) <= &26631) /\
     (!i. i < 256 ==> ival(VR i) = ival(word_sub (VD i) (WI i)) rem &3329)
     ==> nsum {i | i < 256}
              (\i. ((4 * val(VR i) + 3329) DIV 6658) MOD 2 * 2 EXP i) =
         num_of_bytelist(kpke_decrypt mlkem1024 dk ct)`;;

let KPKE_DECRYPT_K4_RESULT = assume_spec KPKE_DECRYPT_K4_RESULT_STMT;;

(*** The modulus check of an encapsulation key for k = 4 (FIPS 203
 *** section 7.2) as the bound of its 12-bit fields
 ***)

let MLKEM_EK_CHECK_1024_STMT =
  `!ek. LENGTH ek = 1568
        ==> (mlkem_ek_check mlkem1024 ek <=>
             !i. i < 1024
                 ==> (num_of_bytelist ek DIV 2 EXP (12 * i)) MOD 2 EXP 12
                     < 3329)`;;

let MLKEM_EK_CHECK_1024 = assume_spec MLKEM_EK_CHECK_1024_STMT;;

(* ------------------------------------------------------------------------- *)
(* The vectors as blocks: polynomial j of a vector as a function of j and of *)
(* the index of the coefficient, and the K-PKE results in that form.         *)
(* ------------------------------------------------------------------------- *)

(*** Coefficient i of polynomial j of a vector at index 256 * j + i ***)

let DIVMOD_256_BLOCK_STMT =
  `!j i. i < 256 ==> (256 * j + i) DIV 256 = j /\ (256 * j + i) MOD 256 = i`;;

let DIVMOD_256_BLOCK = assume_spec DIVMOD_256_BLOCK_STMT;;

let DIVMOD_LT_BLOCK_STMT =
  `!n k i. i < n * k ==> i DIV n < k /\ i MOD n < n`;;

let DIVMOD_LT_BLOCK = assume_spec DIVMOD_LT_BLOCK_STMT;;

(*** The length of a slice of a byte list ***)

let LENGTH_MLKEM_SLICE_STMT =
  `!a n (l:byte list). LENGTH(mlkem_slice a n l) = n`;;

let LENGTH_MLKEM_SLICE = assume_spec LENGTH_MLKEM_SLICE_STMT;;

(*** Evaluation of x DIV n and x MOD n (n a numeral) where x is c + t (c a
 *** numeral multiple of n), n * j + t, or t, given t < n from the
 *** assumptions; the terms that cannot be evaluated are left alone
 ***)

let DIVMOD_EVAL_TAC (asl,w as gl) =
  let is_dm t = match t with
      Comb(Comb(Const(("DIV"|"MOD"),_),_),n) -> is_numeral n
    | _ -> false in
  let tms = setify(find_terms is_dm w) in
  let attempt tm =
    let op = fst(dest_const(rator(rator tm))) and x = rand(rator tm)
    and n = rand tm in
    let nv = dest_numeral n in
    let q,r =
      if is_binary "+" x then
        let a = lhand x and t = rand x in
        if is_numeral a then mk_numeral(quo_num (dest_numeral a) nv),t
        else if is_binary "*" a && lhand a = n then rand a,t
        else `0`,x
      else `0`,x in
    let goal = mk_eq(tm,if op = "DIV" then q else r) in
    let tac = if op = "DIV"
              then MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC r THEN ASM_ARITH_TAC
              else MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC q THEN
                   ASM_ARITH_TAC in
    TAC_PROOF((asl,goal),tac) in
  let ths = mapfilter attempt tms in
  REWRITE_TAC ths gl;;

(*** The statement of the K-PKE key generation in terms of the polynomials
 *** of the vectors and their blocks of coefficients (functions of the
 *** index of the polynomial and of the coefficient)
 ***)

let api_param k = match k with
    2 -> "mlkem512" | 3 -> "mlkem768" | _ -> "mlkem1024";;

let api_eta1 k = if k = 2 then 3 else 2;;

let kpke_keygen_blocks_tm k =
  let ks = string_of_int k and es = string_of_int(api_eta1 k) in
  let a c =
    "mlkem_sample_ntt (APPEND rho [word "^string_of_int c^"; word r])" in
  let ev c = let cs = string_of_int c in
    "("^a c^" (2 * p + 1) * ival((MC:num->num->int16) "^cs^" p) + "^
    a c^" (2 * p) * ival((SH:num->num->int16) "^cs^" (2 * p)))" in
  let od c = let cs = string_of_int c in
    "("^a c^" (2 * p + 1) * ival((SH:num->num->int16) "^cs^" (2 * p)) + "^
    a c^" (2 * p) * ival((SH:num->num->int16) "^cs^" (2 * p + 1)))" in
  let sum f = String.concat " + " (map f (rev(0--(k-1)))) in
  parse_term(
   "!d rho sigma (SH:num->num->int16) (EH:num->num->int16) "^
   "(MC:num->num->int16) (PT:num->num->int16) (PU:num->num->int16) "^
   "(TR:num->num->int16) (SR:num->num->int16). "^
   "mlkem_g(APPEND d [word "^ks^"]) = rho,sigma /\\ "^
   "(!i j n. i < "^ks^" /\\ j < "^ks^" /\\ n < 256 ==> "^
   "  mlkem_sample_ntt (APPEND rho [word j; word i]) n < &3329) /\\ "^
   "(!j i. j < "^ks^" /\\ i < 256 ==> "^
   "  (ival(SH j i) == mlkem_ntt (mlkem_cbd "^es^" (mlkem_prf "^es^
   "   sigma (word j))) i) (mod &3329) /\\ abs(ival(SH j i)) <= &23594) /\\ "^
   "(!j i. j < "^ks^" /\\ i < 256 ==> "^
   "  (ival(EH j i) == mlkem_ntt (mlkem_cbd "^es^" (mlkem_prf "^es^
   "   sigma (word("^ks^" + j)))) i) (mod &3329) /\\ "^
   "  abs(ival(EH j i)) <= &23594) /\\ "^
   "(!j p. j < "^ks^" /\\ p < 128 ==> "^
   "  (ival(MC j p) == ival(SH j (2 * p + 1)) * "^
   "   &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\\ "^
   "(!r p. r < "^ks^" /\\ p < 128 ==> "^
   "  (ival(PT r (2 * p)) == &169 * ("^sum ev^")) (mod &3329) /\\ "^
   "  (ival(PT r (2 * p + 1)) == &169 * ("^sum od^")) (mod &3329)) /\\ "^
   "(!r i. r < "^ks^" /\\ i < 256 ==> "^
   "  (ival(PU r i) == &65536 * ival(PT r i)) (mod &3329) /\\ "^
   "  abs(ival(PU r i)) <= &3328) /\\ "^
   "(!r i. r < "^ks^" /\\ i < 256 ==> "^
   "  ival(TR r i) = ival(word_add (PU r i) (EH r i)) rem &3329) /\\ "^
   "(!r i. r < "^ks^" /\\ i < 256 ==> ival(SR r i) = ival(SH r i) rem &3329) "^
   "==> num_of_wordlist(MAP (word_zx:int16->12 word) "^
   "      (list_of_seq (\\i. TR (i DIV 256) (i MOD 256)) "^
   string_of_int(256 * k)^")) + "^
   "    2 EXP (8 * "^string_of_int(384 * k)^") * num_of_bytelist rho = "^
   "    num_of_bytelist(FST(kpke_keygen "^api_param k^" d)) /\\ "^
   "    num_of_wordlist(MAP (word_zx:int16->12 word) "^
   "      (list_of_seq (\\i. SR (i DIV 256) (i MOD 256)) "^
   string_of_int(256 * k)^")) = "^
   "    num_of_bytelist(SND(kpke_keygen "^api_param k^" d))");;

let KPKE_KEYGEN_BLOCKS_TAC flat =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC flat THEN
  MAP_EVERY EXISTS_TAC
   [`sigma:byte list`; `\i. (SH:num->num->int16) (i DIV 256) (i MOD 256)`;
    `\i. (EH:num->num->int16) (i DIV 256) (i MOD 256)`;
    `\i. (MC:num->num->int16) (i DIV 128) (i MOD 128)`;
    `\i. (PT:num->num->int16) (i DIV 256) (i MOD 256)`;
    `\i. (PU:num->num->int16) (i DIV 256) (i MOD 256)`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  DIVMOD_EVAL_TAC THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC DIVMOD_LT_BLOCK THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];;

(*** The arithmetic of the coefficients of encryption: 16-bit sums in
 *** range, the coefficients 0 or 1665 of the message, the remainders mod q,
 *** and the two additions to v (the noise e2 and the message) with only
 *** the second reduced
 ***)

let IVAL_WORD_ADD_INRANGE_STMT =
  `!x y:int16. abs(ival x + ival y) < &32768
               ==> ival(word_add x y) = ival x + ival y`;;

let IVAL_WORD_ADD_INRANGE = assume_spec IVAL_WORD_ADD_INRANGE_STMT;;

let MU_CASES_STMT =
  `!n i. word((3329 * (n DIV 2 EXP i) MOD 2 + 1) DIV 2):int16 = word 0 \/
         word((3329 * (n DIV 2 EXP i) MOD 2 + 1) DIV 2):int16 = word 1665`;;

let MU_CASES = assume_spec MU_CASES_STMT;;

let REM_3329_BOUNDS_STMT =
  `!y. &0 <= y rem &3329 /\ y rem &3329 < &3329`;;

let REM_3329_BOUNDS = assume_spec REM_3329_BOUNDS_STMT;;

let V_TWO_STEP_STMT =
  `!(v1:int16) (e2:int16) (mu:int16) (v2:int16) (v4:int16).
     abs(ival v1) <= &26631 /\ abs(ival e2) <= &2 /\
     (mu = word 0 \/ mu = word 1665) /\
     ival v2 = ival(word_add v1 e2) rem &3329 /\
     ival v4 = ival(word_add v2 mu) rem &3329
     ==> ival v4 = ival(word_add (word_add v1 e2) mu) rem &3329`;;

let V_TWO_STEP = assume_spec V_TWO_STEP_STMT;;

(*** An index as block and offset ***)

let DIVMOD_256_RECOMB_STMT =
  `!i. 256 * (i DIV 256) + i MOD 256 = i`;;

let DIVMOD_256_RECOMB = assume_spec DIVMOD_256_RECOMB_STMT;;

(*** The NTTs only use the first 256 coefficients ***)

let FORWARD_NTT_LOCAL_STMT =
  `!f g k. (!n. n < 256 ==> f n = g n) ==> forward_ntt f k = forward_ntt g k`;;

let FORWARD_NTT_LOCAL = assume_spec FORWARD_NTT_LOCAL_STMT;;

let INVERSE_NTT_LOCAL_STMT =
  `!f g k. (!n. n < 256 ==> f n = g n) ==> inverse_ntt f k = inverse_ntt g k`;;

let INVERSE_NTT_LOCAL = assume_spec INVERSE_NTT_LOCAL_STMT;;

let FORWARD_NTT_BLOCK_STMT =
  `!(U:num->num->int16) j k.
     forward_ntt (\n. ival(U ((256 * j + n) DIV 256) ((256 * j + n) MOD 256)))
                 k =
     forward_ntt (\n. ival(U j n)) k`;;

let FORWARD_NTT_BLOCK = assume_spec FORWARD_NTT_BLOCK_STMT;;

let INVERSE_NTT_BLOCK_STMT =
  `!(U:num->num->int16) j k.
     inverse_ntt (\n. ival(U ((256 * j + n) DIV 256) ((256 * j + n) MOD 256)))
                 k =
     inverse_ntt (\n. ival(U j n)) k`;;

let INVERSE_NTT_BLOCK = assume_spec INVERSE_NTT_BLOCK_STMT;;

(*** A coefficient reduced mod q as an unsigned value below q ***)

let VAL_LT_OF_REM_STMT =
  `!x:int16 y. ival x = y rem &3329 ==> val x < 3329`;;

let VAL_LT_OF_REM = assume_spec VAL_LT_OF_REM_STMT;;

(*** The statement of K-PKE encryption for k in terms of the polynomials of
 *** the vectors and their blocks of coefficients
 ***)

let api_du k = if k = 4 then 11 else 10;;
let api_dv k = if k = 4 then 5 else 4;;

let kpke_encrypt_blocks_tm k =
  let ks = string_of_int k and es = string_of_int(api_eta1 k) in
  let n x = string_of_int x in
  let rho = "(mlkem_slice "^n(384 * k)^" 32 ek)" in
  let a c = "mlkem_sample_ntt (APPEND "^rho^" [word q; word "^n c^"])" in
  let ev c = let cs = n c in
    "("^a c^" (2 * p + 1) * ival((MC:num->num->int16) "^cs^" p) + "^
    a c^" (2 * p) * ival((YH:num->num->int16) "^cs^" (2 * p)))" in
  let od c = let cs = n c in
    "("^a c^" (2 * p + 1) * ival((YH:num->num->int16) "^cs^" (2 * p)) + "^
    a c^" (2 * p) * ival((YH:num->num->int16) "^cs^" (2 * p + 1)))" in
  let tev c = let cs = n c in
    "(ival((TT:num->num->int16) "^cs^" (2 * p + 1)) * ival(MC "^cs^" p) + "^
    "ival(TT "^cs^" (2 * p)) * ival(YH "^cs^" (2 * p)))" in
  let tod c = let cs = n c in
    "(ival((TT:num->num->int16) "^cs^" (2 * p + 1)) * "^
    "ival(YH "^cs^" (2 * p)) + "^
    "ival(TT "^cs^" (2 * p)) * ival(YH "^cs^" (2 * p + 1)))" in
  let sum f = String.concat " + " (map f (rev(0--(k-1)))) in
  let du = api_du k and dv = api_dv k in
  let p2 x = n(1 lsl x) in
  parse_term(
   "!ek m r (TT:num->num->int16) (YH:num->num->int16) (MC:num->num->int16) "^
   "(E1:num->num->int16) (E2:num->int16) (MU:num->int16) "^
   "(U0:num->num->int16) (V0:num->int16) (U1:num->num->int16) "^
   "(V1:num->int16) (U3:num->num->int16) (V2:num->int16) (V4:num->int16). "^
   "(!i j n. i < "^ks^" /\\ j < "^ks^" /\\ n < 256 ==> "^
   "  mlkem_sample_ntt (APPEND "^rho^" [word j; word i]) n < &3329) /\\ "^
   "(!j i. j < "^ks^" /\\ i < 256 ==> "^
   "  TT j i = word((num_of_bytelist ek DIV 2 EXP (12 * (256 * j + i))) "^
   "               MOD 2 EXP 12)) /\\ "^
   "(!j i. j < "^ks^" /\\ i < 256 ==> "^
   "  (ival(YH j i) == mlkem_ntt (mlkem_cbd "^es^" (mlkem_prf "^es^
   "   r (word j))) i) (mod &3329) /\\ abs(ival(YH j i)) <= &23594) /\\ "^
   "(!j p. j < "^ks^" /\\ p < 128 ==> "^
   "  (ival(MC j p) == ival(YH j (2 * p + 1)) * "^
   "   &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\\ "^
   "(!j i. j < "^ks^" /\\ i < 256 ==> "^
   "  (ival(E1 j i) == coeff i (mlkem_cbd 2 (mlkem_prf 2 r (word("^ks^
   " + j))))) (mod &3329) /\\ abs(ival(E1 j i)) <= &2) /\\ "^
   "(!i. i < 256 ==> "^
   "  (ival(E2 i) == coeff i (mlkem_cbd 2 (mlkem_prf 2 r (word "^n(2 * k)^
   ")))) (mod &3329) /\\ abs(ival(E2 i)) <= &2) /\\ "^
   "(!i. i < 256 ==> "^
   "  MU i = word((3329 * (num_of_bytelist m DIV 2 EXP i) MOD 2 + 1) "^
   "             DIV 2)) /\\ "^
   "(!q p. q < "^ks^" /\\ p < 128 ==> "^
   "  (ival(U0 q (2 * p)) == &169 * ("^sum ev^")) (mod &3329) /\\ "^
   "  (ival(U0 q (2 * p + 1)) == &169 * ("^sum od^")) (mod &3329)) /\\ "^
   "(!p. p < 128 ==> "^
   "  (ival(V0(2 * p)) == &169 * ("^sum tev^")) (mod &3329) /\\ "^
   "  (ival(V0(2 * p + 1)) == &169 * ("^sum tod^")) (mod &3329)) /\\ "^
   "(!j i. j < "^ks^" /\\ i < 256 ==> "^
   "  (ival(U1 j i) == inverse_ntt (\\n. ival(U0 j n)) i) (mod &3329) /\\ "^
   "  abs(ival(U1 j i)) <= &26631) /\\ "^
   "(!i. i < 256 ==> (ival(V1 i) == inverse_ntt (\\n. ival(V0 n)) i) "^
   "  (mod &3329) /\\ abs(ival(V1 i)) <= &26631) /\\ "^
   "(!j i. j < "^ks^" /\\ i < 256 ==> "^
   "  ival(U3 j i) = ival(word_add (U1 j i) (E1 j i)) rem &3329) /\\ "^
   "(!i. i < 256 ==> "^
   "  ival(V2 i) = ival(word_add (V1 i) (E2 i)) rem &3329) /\\ "^
   "(!i. i < 256 ==> ival(V4 i) = ival(word_add (V2 i) (MU i)) rem &3329) "^
   "==> nsum {i | i < "^n(256 * k)^"} "^
   "      (\\i. (("^p2(du+1)^" * val(U3 (i DIV 256) (i MOD 256)) + 3329) "^
   "           DIV 6658) MOD "^p2 du^" * 2 EXP ("^n du^" * i)) + "^
   "    2 EXP (8 * "^n(32 * du * k)^") * "^
   "    nsum {i | i < 256} "^
   "      (\\i. (("^p2(dv+1)^" * val(V4 i) + 3329) DIV 6658) MOD "^p2 dv^
   "           * 2 EXP ("^n dv^" * i)) = "^
   "    num_of_bytelist(kpke_encrypt "^api_param k^" ek m r)");;

let KPKE_ENCRYPT_BLOCKS_TAC flat =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC flat THEN
  MAP_EVERY EXISTS_TAC
   [`\i. (TT:num->num->int16) (i DIV 256) (i MOD 256)`;
    `\i. (YH:num->num->int16) (i DIV 256) (i MOD 256)`;
    `\i. (MC:num->num->int16) (i DIV 128) (i MOD 128)`;
    `\i. (E1:num->num->int16) (i DIV 256) (i MOD 256)`;
    `E2:num->int16`; `MU:num->int16`;
    `\i. (U0:num->num->int16) (i DIV 256) (i MOD 256)`; `V0:num->int16`;
    `\i. (U1:num->num->int16) (i DIV 256) (i MOD 256)`; `V1:num->int16`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST
   [(* v reduced twice *)
    MATCH_MP_TAC V_TWO_STEP THEN EXISTS_TAC `(V2:num->int16) i` THEN
    ASM_SIMP_TAC[MU_CASES] THEN NO_TAC;
    DIVMOD_EVAL_TAC THEN REWRITE_TAC[FORWARD_NTT_BLOCK; INVERSE_NTT_BLOCK] THEN
    ASM_SIMP_TAC[] THEN
    FIRST
     [(* the encoded t, from the blocks by i = 256 * (i DIV 256) + i MOD 256 *)
      FIRST_X_ASSUM(fun th ->
        if can (find_term (fun t -> t = `TT:num->num->int16`)) (concl th) &&
           is_forall(concl th)
        then MP_TAC(SPECL [`i DIV 256`; `i MOD 256`] th) THEN
             ANTS_TAC THENL
              [MATCH_MP_TAC DIVMOD_LT_BLOCK THEN CONV_TAC NUM_REDUCE_CONV THEN
               ASM_REWRITE_TAC[];
               REWRITE_TAC[DIVMOD_256_RECOMB]] THEN NO_TAC
        else NO_TAC);
      FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC DIVMOD_LT_BLOCK THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]]];;

(*** The 12-bit fields of a 384-byte slice of ek ***)

let FIELD_OF_SLICE_STMT =
  `!x j i. i < 256
           ==> (((x DIV 2 EXP (8 * (384 * j))) MOD 2 EXP (8 * 384)) DIV
                2 EXP (12 * i)) MOD 2 EXP 12 =
               (x DIV 2 EXP (12 * (256 * j + i))) MOD 2 EXP 12`;;

let FIELD_OF_SLICE = assume_spec FIELD_OF_SLICE_STMT;;

let FIELD_OF_SLICE_EK_STMT =
  `!ek j i. 384 * j + 384 <= LENGTH ek /\ i < 256
            ==> (num_of_bytelist(mlkem_slice (384 * j) 384 ek) DIV
                 2 EXP (12 * i)) MOD 2 EXP 12 =
                (num_of_bytelist ek DIV 2 EXP (12 * (256 * j + i))) MOD
                2 EXP 12`;;

let FIELD_OF_SLICE_EK = assume_spec FIELD_OF_SLICE_EK_STMT;;

(*** The d-bit fields of an m-byte slice, 8 * m = 256 * d ***)

let FIELD_OF_SLICE_GEN_STMT =
  `!x m d j i. 8 * m = d * 256 /\ i < 256
               ==> (((x DIV 2 EXP (8 * (m * j))) MOD 2 EXP (8 * m)) DIV
                    2 EXP (d * i)) MOD 2 EXP d =
                   (x DIV 2 EXP (d * (256 * j + i))) MOD 2 EXP d`;;

let FIELD_OF_SLICE_GEN = assume_spec FIELD_OF_SLICE_GEN_STMT;;

let FIELD_OF_SLICE_BYTES_STMT =
  `!l m d j i. 8 * m = d * 256 /\ m * j + m <= LENGTH l /\ i < 256
               ==> (num_of_bytelist(mlkem_slice (m * j) m l) DIV
                    2 EXP (d * i)) MOD 2 EXP d =
                   (num_of_bytelist l DIV 2 EXP (d * (256 * j + i))) MOD
                   2 EXP d`;;

let FIELD_OF_SLICE_BYTES = assume_spec FIELD_OF_SLICE_BYTES_STMT;;

(*** The blocked statement of K-PKE decryption ***)

let kpke_decrypt_blocks_tm k =
  let ks = string_of_int k and n x = string_of_int x in
  let du = api_du k and dv = api_dv k in
  let sum f = String.concat " + " (map f (rev(0--(k-1)))) in
  let tev c = let cs = n c in
    "(ival((SV:num->num->int16) "^cs^" (2 * p + 1)) * ival(MC "^cs^" p) + "^
    "ival(SV "^cs^" (2 * p)) * ival(UH "^cs^" (2 * p)))" in
  let tod c = let cs = n c in
    "(ival((SV:num->num->int16) "^cs^" (2 * p + 1)) * "^
    "ival(UH "^cs^" (2 * p)) + "^
    "ival(SV "^cs^" (2 * p)) * ival(UH "^cs^" (2 * p + 1)))" in
  parse_term(
   "!dk ct (UD:num->num->int16) (VD:num->int16) (SV:num->num->int16) "^
   "(UH:num->num->int16) (MC:num->num->int16) (WP:num->int16) "^
   "(WI:num->int16) (VR:num->int16). "^
   "(!j i. j < "^ks^" /\\ i < 256 ==> UD j i = "^
   "  word((3329 * (num_of_bytelist ct DIV 2 EXP ("^n du^
   " * (256 * j + i))) MOD 2 EXP "^n du^" + "^n(1 lsl (du-1))^") DIV "^
   n(1 lsl du)^")) /\\ "^
   "(!i. i < 256 ==> VD i = "^
   "  word((3329 * (num_of_bytelist(mlkem_slice "^n(32 * du * k)^" "^
   n(32 * dv)^" ct) DIV 2 EXP ("^n dv^" * i)) MOD 2 EXP "^n dv^" + "^
   n(1 lsl (dv-1))^") DIV "^n(1 lsl dv)^")) /\\ "^
   "(!j i. j < "^ks^" /\\ i < 256 ==> "^
   "  SV j i = word((num_of_bytelist dk DIV 2 EXP (12 * (256 * j + i))) "^
   "               MOD 2 EXP 12)) /\\ "^
   "(!j i. j < "^ks^" /\\ i < 256 ==> "^
   "  (ival(UH j i) == forward_ntt (\\n. ival(UD j n)) i) (mod &3329) /\\ "^
   "  abs(ival(UH j i)) <= &23594) /\\ "^
   "(!j p. j < "^ks^" /\\ p < 128 ==> "^
   "  (ival(MC j p) == ival(UH j (2 * p + 1)) * "^
   "   &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\\ "^
   "(!p. p < 128 ==> "^
   "  (ival(WP(2 * p)) == &169 * ("^sum tev^")) (mod &3329) /\\ "^
   "  (ival(WP(2 * p + 1)) == &169 * ("^sum tod^")) (mod &3329)) /\\ "^
   "(!i. i < 256 ==> (ival(WI i) == inverse_ntt (\\n. ival(WP n)) i) "^
   "  (mod &3329) /\\ abs(ival(WI i)) <= &26631) /\\ "^
   "(!i. i < 256 ==> ival(VR i) = ival(word_sub (VD i) (WI i)) rem &3329) "^
   "==> nsum {i | i < 256} "^
   "      (\\i. ((4 * val(VR i) + 3329) DIV 6658) MOD 2 * 2 EXP i) = "^
   "    num_of_bytelist(kpke_decrypt "^api_param k^" dk ct)");;

let KPKE_DECRYPT_BLOCKS_TAC flat =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC flat THEN
  MAP_EVERY EXISTS_TAC
   [`\i. (UD:num->num->int16) (i DIV 256) (i MOD 256)`; `VD:num->int16`;
    `\i. (SV:num->num->int16) (i DIV 256) (i MOD 256)`;
    `\i. (UH:num->num->int16) (i DIV 256) (i MOD 256)`;
    `\i. (MC:num->num->int16) (i DIV 128) (i MOD 128)`;
    `WP:num->int16`; `WI:num->int16`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  DIVMOD_EVAL_TAC THEN REWRITE_TAC[FORWARD_NTT_BLOCK; INVERSE_NTT_BLOCK] THEN
  ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && length(fst(strip_forall(concl th))) = 2
    then MP_TAC(SPECL [`i DIV 256`; `i MOD 256`] th) THEN
         ANTS_TAC THENL
          [MATCH_MP_TAC DIVMOD_LT_BLOCK THEN CONV_TAC NUM_REDUCE_CONV THEN
           ASM_REWRITE_TAC[];
           REWRITE_TAC[DIVMOD_256_RECOMB]] THEN NO_TAC
    else NO_TAC);;

(*** The blocked statements for k = 2, 3 and 4 ***)

let KPKE_KEYGEN_K2_BLOCKS_STMT =
  kpke_keygen_blocks_tm 2;;

let KPKE_KEYGEN_K2_BLOCKS = assume_spec KPKE_KEYGEN_K2_BLOCKS_STMT;;

let KPKE_KEYGEN_K3_BLOCKS_STMT =
  kpke_keygen_blocks_tm 3;;

let KPKE_KEYGEN_K3_BLOCKS = assume_spec KPKE_KEYGEN_K3_BLOCKS_STMT;;

let KPKE_KEYGEN_K4_BLOCKS_STMT =
  kpke_keygen_blocks_tm 4;;

let KPKE_KEYGEN_K4_BLOCKS = assume_spec KPKE_KEYGEN_K4_BLOCKS_STMT;;

let KPKE_ENCRYPT_K2_BLOCKS_STMT =
  kpke_encrypt_blocks_tm 2;;

let KPKE_ENCRYPT_K2_BLOCKS = assume_spec KPKE_ENCRYPT_K2_BLOCKS_STMT;;

let KPKE_ENCRYPT_K3_BLOCKS_STMT =
  kpke_encrypt_blocks_tm 3;;

let KPKE_ENCRYPT_K3_BLOCKS = assume_spec KPKE_ENCRYPT_K3_BLOCKS_STMT;;

let KPKE_ENCRYPT_K4_BLOCKS_STMT =
  kpke_encrypt_blocks_tm 4;;

let KPKE_ENCRYPT_K4_BLOCKS = assume_spec KPKE_ENCRYPT_K4_BLOCKS_STMT;;

let KPKE_DECRYPT_K2_BLOCKS_STMT =
  kpke_decrypt_blocks_tm 2;;

let KPKE_DECRYPT_K2_BLOCKS = assume_spec KPKE_DECRYPT_K2_BLOCKS_STMT;;

let KPKE_DECRYPT_K3_BLOCKS_STMT =
  kpke_decrypt_blocks_tm 3;;

let KPKE_DECRYPT_K3_BLOCKS = assume_spec KPKE_DECRYPT_K3_BLOCKS_STMT;;

let KPKE_DECRYPT_K4_BLOCKS_STMT =
  kpke_decrypt_blocks_tm 4;;

let KPKE_DECRYPT_K4_BLOCKS = assume_spec KPKE_DECRYPT_K4_BLOCKS_STMT;;
