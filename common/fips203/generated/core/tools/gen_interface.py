#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
"""Generate interface.ml, stubs.ml and check.ml for the equivalence proofs.

interface.ml  states every lemma that one proof file uses from another, as
              NAME_STMT terms, with the file that must prove it (its owner).
stubs.ml      asserts every statement with mk_thm. Development only: it lets
              each owner work before the files it depends on are finished.
              It is never loaded by all.ml.
check.ml      checks after loading all proof files that each NAME is a
              theorem without hypotheses whose conclusion is NAME_STMT.

Run from anywhere: python3 common/fips203/generated/core/tools/gen_interface.py.
It writes interface.ml, stubs.ml and check.ml next to tools/ and the statements
that carry the claim into ../fips203_equivalence.ml.
"""

import os

PARAMS = [
    dict(k=2, name="MLKEM512", p="mlkem512", eta1=3, eta2=2, du=10, dv=4),
    dict(k=3, name="MLKEM768", p="mlkem768", eta1=2, eta2=2, du=10, dv=4),
    dict(k=4, name="MLKEM1024", p="mlkem1024", eta1=2, eta2=2, du=11, dv=5),
]

for P in PARAMS:
    k, du, dv = P["k"], P["du"], P["dv"]
    P.update(T=384 * k, EK=384 * k + 32, C=32 * (du * k + dv), DK=768 * k + 96,
             CU=32 * du * k, RHO_DK=768 * k, K256=256 * k, Q_DU=2 ** du,
             NB=P["name"][5:])

ENTRIES = []  # (name, owner, statement)


def add(owner, name, stmt):
    ENTRIES.append((name, owner, stmt.strip("\n")))


# ---------------------------------------------------------------------------
# foundation.ml: monad, loops, lists, arithmetic, residues, small primitives
# ---------------------------------------------------------------------------

F = "foundation"
add(F, "NATIVE_BIND_VALUE", r"""
!(x:A) (f:A->(B)native_result). native_bind (Value x) f = f x""")
add(F, "NATIVE_BIND_FAULT", r"""
!(e:fault) (f:A->(B)native_result).
  native_bind (Fault e:(A)native_result) f = Fault e""")
add(F, "NATIVE_FOLDL_VALUE", r"""
!(body:I->S->(S)native_result) (g:I->S->S) (P:S->bool) (l:I list) (s:S).
  P s /\ (!x t. MEM x l /\ P t ==> body x t = Value (g x t) /\ P (g x t))
  ==> native_foldl body l s = Value (equiv_foldl g s l)""")
add(F, "NATIVE_FOLDL_FILL", r"""
!(body:int->(A)list->((A)list)native_result) (f:num->A) n (s:A list).
  LENGTH s = n /\
  (!i t. i < n /\ LENGTH t = n
         ==> body (&i) t = Value (isa_list_update t i (f i)))
  ==> native_foldl body (list_of_seq (\i. &i) n) s = Value (list_of_seq f n)""")
add(F, "NATIVE_SCHEDULE_UPTO", r"""
!fuel a n.
  n - a < fuel
  ==> native_schedule fuel (\i. int_lt i (&n)) (\i. int_add i (&1)) (&a) =
      list_of_seq (\i. &(a + i)) (n - a)""")
add(F, "NATIVE_SCHEDULE_STEP", r"""
!fuel n d.
  0 < d /\ n < fuel
  ==> native_schedule fuel (\i. int_lt i (&n)) (\i. int_add i (&d)) (&0) =
      list_of_seq (\i. &(d * i)) ((n + d - 1) DIV d)""")
add(F, "NATIVE_SCHEDULE_NTTINV", r"""
native_schedule 128 (\len. int_lt len (&129)) (int_mul (&2)) (&2) =
[&2; &4; &8; &16; &32; &64; &128]""")
add(F, "NATIVE_LIST_INDEX", r"""
!(xs:A list) n.
  n < LENGTH xs
  ==> typed_hol_read (native_list_index xs (&n)) = Value (EL n xs)""")
add(F, "NATIVE_LIST_UPDATE", r"""
!(xs:A list) n (v:A).
  n < LENGTH xs
  ==> typed_hol_read (native_list_update xs (&n) v) =
      Value (isa_list_update xs n v)""")
add(F, "LENGTH_ISA_LIST_UPDATE", r"""
!(xs:A list) n (v:A). LENGTH (isa_list_update xs n v) = LENGTH xs""")
add(F, "EL_ISA_LIST_UPDATE", r"""
!(xs:A list) n (v:A) i.
  i < LENGTH xs
  ==> EL i (isa_list_update xs n v) = if i = n then v else EL i xs""")
add(F, "NOMINAL_UPDATE_POLY", r"""
!(l:fips203_zq list) n v.
  n < LENGTH l
  ==> typed_hol_read
       (typed_hol_nominal_update
         (FIPS203_Poly:fips203_zq list->(P)fips203_poly)
         fips203_poly_coefficients
         (\nf. native_list_update nf (&n) v)
         (FIPS203_Poly l)) =
      Value (FIPS203_Poly (isa_list_update l n v))""")
add(F, "NOMINAL_UPDATE_VEC", r"""
!(l:B list) n (v:B).
  n < LENGTH l
  ==> typed_hol_read
       (typed_hol_nominal_update
         (Common_Vec:B list->(A,B)common_vec)
         common_vec_entries
         (\nf. native_list_update nf (&n) v)
         (Common_Vec l)) =
      Value (Common_Vec (isa_list_update l n v))""")
add(F, "NOMINAL_UPDATE_MAT", r"""
!(l:C list) n (v:C).
  n < LENGTH l
  ==> typed_hol_read
       (typed_hol_nominal_update
         (Common_Mat:(R,K,C)fips_matrix->(R,K,C)common_mat)
         common_mat_entries
         (typed_hol_nominal_update FIPS_Matrix fips_matrix_entries
            (\nf. native_list_update nf (&n) v))
         (Common_Mat (FIPS_Matrix l))) =
      Value (Common_Mat (FIPS_Matrix (isa_list_update l n v)))""")
add(F, "ISA_UPT", r"""
!m n. isa_upt m n = list_of_seq (\i. m + i) (n - m)""")
add(F, "ISA_NAT_NUM", r"""
!n. isa_nat (&n) = n""")
add(F, "ISA_INT_MOD_POS", r"""
!a b. &0 < b ==> isa_int_mod a b = a rem b""")
add(F, "ISA_INT_DIV_POS", r"""
!a b. &0 < b ==> isa_int_div a b = a div b""")
add(F, "INT_ARITH_ADIV", r"""
!a b. &0 < b ==> typed_hol_int_arithmetic ADiv a b = Value (a div b)""")
add(F, "INT_ARITH_AQUOT", r"""
!a b. &0 < b /\ a rem b = &0
      ==> typed_hol_int_arithmetic AQuot a b = Value (a div b)""")
add(F, "INT_ARITH_APOW", r"""
!a n. typed_hol_int_arithmetic APow a (&n) = Value (a pow n)""")
add(F, "TYPED_HOL_POW_MOD", r"""
!a e m. 0 < m ==> typed_hol_pow_mod a (&e) (&m) = Value ((a pow e) rem &m)""")
add(F, "TYPED_HOL_NONNEGATIVE", r"""
!n. typed_hol_nonnegative (&n) = Value (&n)""")
add(F, "TYPED_HOL_INT_TO_BYTE", r"""
!n. n < 256 ==> typed_hol_int_to_byte (&n) = Value (word n:byte)""")
add(F, "TYPED_HOL_INT_TO_BIT", r"""
!b. typed_hol_int_to_bit (&(bitval b)) = Value b""")
add(F, "TYPED_HOL_INT_TO_BIT_CLAUSES", r"""
typed_hol_int_to_bit (&0) = Value F /\ typed_hol_int_to_bit (&1) = Value T""")
add(F, "TYPED_HOL_BIT_VALUE", r"""
!b. typed_hol_bit_value b = Value (&(bitval b))""")
add(F, "SEQUENCE_EXTENT", r"""
!n (xs:A list). LENGTH xs = n ==> typed_hol_sequence_extent n xs = Value xs""")
add(F, "LIST_SLICE", r"""
!(xs:A list) a u.
  a <= u /\ u <= LENGTH xs
  ==> typed_hol_read (typed_hol_list_slice xs (&a) (&u)) =
      Value (list_of_seq (\i. EL (a + i) xs) (u - a))""")
add(F, "LIST_SLICE_BYTES", r"""
!(xs:byte list) a u.
  a <= u /\ u <= LENGTH xs
  ==> typed_hol_read (typed_hol_list_slice xs (&a) (&u)) =
      Value (mlkem_slice a (u - a) xs)""")
add(F, "RESIDUE_OF_INT_MOD_REP", r"""
!v. residue_rep (residue_of_int_mod v:(N)residue) =
    num_of_int (v rem &(dimindex(:N)))""")
add(F, "FZ_RESIDUE_OF_INT_MOD", r"""
!v. fz (FIPS203_Zq (residue_of_int_mod v)) = v rem &3329""")
add(F, "FZ_POS", r"""
!z. &0 <= fz z""")
add(F, "LENGTH_ZQLIST", r"""
!a. LENGTH (zqlist a) = 256""")
add(F, "EL_ZQLIST", r"""
!a i. i < 256 ==> EL i (zqlist a) = FIPS203_Zq (residue_of_int_mod (a i))""")
add(F, "ZARR_ZQLIST", r"""
!a i. i < 256 ==> zarr (zqlist a) i = a i rem &3329""")
add(F, "ZQ_LIST_OK_ZQLIST", r"""
!a. zq_list_ok (zqlist a)""")
add(F, "ZQLIST_ZARR", r"""
!l. zq_list_ok l ==> zqlist (zarr l) = l""")
add(F, "ZQLIST_EQ", r"""
!a b. (!i. i < 256 ==> a i rem &3329 = b i rem &3329) ==> zqlist a = zqlist b""")
add(F, "BITREV7_HOL", r"""
!i. i < 128 ==> BitRev7_hol (&i) = Value (&(bitrev7 i))""")
add(F, "ONEBYTE_HOL", r"""
!n. n < 256 ==> OneByte_hol (&n) = Value [word n:byte]""")
add(F, "G_SEMANTIC", r"""
!x. G_semantic x = Value (mlkem_g x)""")
add(F, "H_SEMANTIC", r"""
!x. H_semantic x = Value (mlkem_h x)""")
add(F, "J_SEMANTIC", r"""
!x. J_semantic x = Value (mlkem_j x)""")
add(F, "PRF_SEMANTIC", r"""
!eta s b. PRF_semantic eta (s,b) = Value (mlkem_prf eta s b)""")

# ---------------------------------------------------------------------------
# bytes.ml: bit/byte conversion, ByteEncode/ByteDecode and their vectors
# ---------------------------------------------------------------------------

B = "bytes"
for N in [32, 128, 160, 192, 320, 352, 384]:
    add(B, "BYTESTOBITS_%d" % N, r"""
!(b:byte list).
  LENGTH b = %d
  ==> BytesToBits_%d_hol b =
      Value (list_of_seq (\i. ODD (num_of_bytelist b DIV 2 EXP i)) %d)""" % (N, N, 8 * N))
for d in [1, 4, 5, 10, 11]:
    add(B, "BYTEDECODE_%d" % d, r"""
!(b:byte list).
  LENGTH b = %d
  ==> ByteDecode_d_%d_%d_hol b =
      Value (list_of_seq (\n. residue_of_int_mod (mlkem_decode %d b n)) 256)""" % (32 * d, d, 2 ** d, d))
    add(B, "BYTEENCODE_%d" % d, r"""
!(l:((%d)residue)list).
  LENGTH l = 256
  ==> ByteEncode_d_%d_hol l =
      Value (mlkem_encode %d 256 (\n. &(residue_rep (EL n l))))""" % (2 ** d, d, d))
add(B, "BYTEDECODE_12", r"""
!(b:byte list).
  LENGTH b = 384
  ==> ByteDecode_d_12_3329_hol b = Value (zqlist (mlkem_decode 12 b))""")
add(B, "BYTEENCODE_12", r"""
!l. LENGTH l = 256
    ==> ByteEncode_d_12_hol l = Value (mlkem_encode 12 256 (zarr l))""")
for P in PARAMS:
    add(B, "ZQBYTEDECODEVECTOR12_%(k)d" % P, r"""
!(b:byte list).
  LENGTH b = %(T)d
  ==> ZqByteDecodeVector12_%(k)d_%(name)s_Configuration_hol b =
      Value (zvec %(k)d (\i. zqlist (\n. mlkem_decode 12 b (256 * i + n))))""" % P)
    add(B, "ZQBYTEENCODEVECTOR12_%(k)d" % P, r"""
!v. (!i. i < %(k)d ==> zq_list_ok (v i))
    ==> ZqByteEncodeVector12_%(k)d_FIPS203_NTT_%(name)s_Configuration_hol
          (zvec %(k)d v) =
        Value (mlkem_encode 12 %(K256)d (\n. zarr (v (n DIV 256)) (n MOD 256)))""" % P)
    add(B, "DECODECOMPRESSEDVECTOR_%(k)d" % P, r"""
!(b:byte list).
  LENGTH b = %(CU)d
  ==> DecodeCompressedVector_d_%(du)d_%(Q_DU)d_%(k)d_%(name)s_Configuration_hol b =
      Value (list_of_seq
              (\i. list_of_seq
                    (\n. residue_of_int_mod (mlkem_decode %(du)d b (256 * i + n)))
                    256)
              %(k)d)""" % P)
    add(B, "ENCODECOMPRESSEDVECTOR_%(k)d" % P, r"""
!(c:(((%(Q_DU)d)residue)list)list).
  LENGTH c = %(k)d /\ (!i. i < %(k)d ==> LENGTH (EL i c) = 256)
  ==> EncodeCompressedVector_d_%(du)d_%(Q_DU)d_%(k)d_%(name)s_Configuration_hol c =
      Value (mlkem_encode %(du)d %(K256)d
               (\n. &(residue_rep (EL (n MOD 256) (EL (n DIV 256) c)))))""" % P)

# ---------------------------------------------------------------------------
# rq.ml: R_q bridge lemmas, Compress/Decompress, CBD, R_q additions
# ---------------------------------------------------------------------------

R = "rq"
add(R, "ZPOLY_IN_RQ", r"""
!l. zpoly l IN ring_carrier mlkem_rq""")
add(R, "COEFF_ZPOLY", r"""
!l i. i < 256 ==> coeff i (zpoly l) = zarr l i rem &3329""")
add(R, "ZPOLY_ZQLIST", r"""
!a. zpoly (zqlist a) = mlkem_poly a""")
add(R, "ZPOLY_ZQLIST_COEFF", r"""
!p. p IN ring_carrier mlkem_rq ==> zpoly (zqlist (\i. coeff i p)) = p""")
for d in [1, 4, 5, 10, 11]:
    add(R, "COMPRESS_%d" % d, r"""
!l. zq_list_ok l
    ==> Compress_d_%d_%d_hol (FIPS203_Poly l) =
        Value (list_of_seq (\n. residue_of_int_mod (mlkem_compress %d (zarr l n))) 256)""" % (d, 2 ** d, d))
    add(R, "DECOMPRESS_%d" % d, r"""
!(y:((%d)residue)list).
  LENGTH y = 256
  ==> Decompress_d_%d_hol y =
      Value (FIPS203_Poly
              (zqlist (\n. mlkem_decompress %d (&(residue_rep (EL n y))))))""" % (2 ** d, d, d))
add(R, "CBD_2", r"""
!(b:byte list).
  LENGTH b = 128
  ==> SamplePolyCBD_eta_2_hol b =
      Value (FIPS203_Poly (zqlist (\n. coeff n (mlkem_cbd 2 b))))""")
add(R, "CBD_3", r"""
!(b:byte list).
  LENGTH b = 192
  ==> SamplePolyCBD_eta_3_hol b =
      Value (FIPS203_Poly (zqlist (\n. coeff n (mlkem_cbd 3 b))))""")
add(R, "RQPOLYADD_HOL_EQ", r"""
!f g. zq_list_ok f /\ zq_list_ok g
      ==> RqPolyAdd_hol (FIPS203_Poly f) (FIPS203_Poly g) =
          Value (FIPS203_Poly
                  (zqlist (\n. coeff n (ring_add mlkem_rq (zpoly f) (zpoly g)))))""")
add(R, "RQPOLYSUB_HOL_EQ", r"""
!f g. zq_list_ok f /\ zq_list_ok g
      ==> RqPolySub_hol (FIPS203_Poly f) (FIPS203_Poly g) =
          Value (FIPS203_Poly
                  (zqlist (\n. coeff n (ring_sub mlkem_rq (zpoly f) (zpoly g)))))""")
for P in PARAMS:
    add(R, "COMPRESSVECTOR_%(k)d" % P, r"""
!v. (!i. i < %(k)d ==> zq_list_ok (v i))
    ==> CompressVector_d_%(du)d_%(Q_DU)d_%(k)d_%(name)s_Configuration_hol (zvec %(k)d v) =
        Value (list_of_seq
                (\i. list_of_seq
                      (\n. residue_of_int_mod (mlkem_compress %(du)d (zarr (v i) n)))
                      256)
                %(k)d)""" % P)
    add(R, "DECOMPRESSVECTOR_%(k)d" % P, r"""
!(c:(((%(Q_DU)d)residue)list)list).
  LENGTH c = %(k)d /\ (!i. i < %(k)d ==> LENGTH (EL i c) = 256)
  ==> DecompressVector_d_%(du)d_%(Q_DU)d_%(k)d_%(name)s_Configuration_hol c =
      Value (zvec %(k)d
              (\i. zqlist
                    (\n. mlkem_decompress %(du)d (&(residue_rep (EL n (EL i c)))))))""" % P)
    add(R, "RQVECTORADD_%(k)d" % P, r"""
!u v. (!i. i < %(k)d ==> zq_list_ok (u i) /\ zq_list_ok (v i))
      ==> RqVectorAdd_%(k)d_%(name)s_Configuration_hol (zvec %(k)d u) (zvec %(k)d v) =
          Value (zvec %(k)d
                  (\i. zqlist
                        (\n. coeff n (ring_add mlkem_rq (zpoly (u i)) (zpoly (v i))))))""" % P)

# ---------------------------------------------------------------------------
# ntt.ml and nttinv.ml: the NTT loops of FIPS 203 Algorithms 9 and 10
# ---------------------------------------------------------------------------

add("ntt", "NTT_HOL_EQ", r"""
!l. zq_list_ok l
    ==> NTT_hol (FIPS203_Poly l) =
        Value (FIPS203_Poly (zqlist (mlkem_ntt (zpoly l))))""")
add("nttinv", "NTTINV_HOL_EQ", r"""
!l. zq_list_ok l
    ==> NTTInv_hol (FIPS203_Poly l) =
        Value (FIPS203_Poly (zqlist (\n. coeff n (mlkem_ntt_inv (zarr l)))))""")
for P in PARAMS:
    add("ntt", "TQVECTORNTT_%(k)d" % P, r"""
!v. (!i. i < %(k)d ==> zq_list_ok (v i))
    ==> TqVectorNTT_%(k)d_%(name)s_Configuration_hol (zvec %(k)d v) =
        Value (zvec %(k)d (\i. zqlist (mlkem_ntt (zpoly (v i)))))""" % P)
    add("nttinv", "TQVECTORNTTINV_%(k)d" % P, r"""
!v. (!i. i < %(k)d ==> zq_list_ok (v i))
    ==> TqVectorNTTInv_%(k)d_%(name)s_Configuration_hol (zvec %(k)d v) =
        Value (zvec %(k)d (\i. zqlist (\n. coeff n (mlkem_ntt_inv (zarr (v i))))))""" % P)

# ---------------------------------------------------------------------------
# sample_ntt.ml: SampleNTT (FIPS 203 Algorithm 7)
# ---------------------------------------------------------------------------

add("sample", "SAMPLENTT_HOL_EQ", r"""
!b. sample_ok b
    ==> SampleNTT_hol b = Value (FIPS203_Poly (zqlist (mlkem_sample_ntt b)))""")

# ---------------------------------------------------------------------------
# tq.ml: arithmetic in T_q, vectors and matrices
# ---------------------------------------------------------------------------

Q = "tq"
add(Q, "MULTIPLYNTTS_HOL_EQ", r"""
!f g. zq_list_ok f /\ zq_list_ok g
      ==> MultiplyNTTs_hol (FIPS203_Poly f) (FIPS203_Poly g) =
          Value (FIPS203_Poly (zqlist (fips203_multiply_ntts (zarr f) (zarr g))))""")
add(Q, "TQPOLYADD_HOL_EQ", r"""
!f g. zq_list_ok f /\ zq_list_ok g
      ==> TqPolyAdd_hol (FIPS203_Poly f) (FIPS203_Poly g) =
          Value (FIPS203_Poly (zqlist (\n. ring_add mlkem_zq (zarr f n) (zarr g n))))""")
for P in PARAMS:
    add(Q, "TQVECTORADD_%(k)d" % P, r"""
!u v. (!i. i < %(k)d ==> zq_list_ok (u i) /\ zq_list_ok (v i))
      ==> TqVectorAdd_%(k)d_%(name)s_Configuration_hol (zvec %(k)d u) (zvec %(k)d v) =
          Value (zvec %(k)d (\i. zqlist (\n. ring_add mlkem_zq (zarr (u i) n) (zarr (v i) n))))""" % P)
    add(Q, "TQVECTORDOT_%(k)d" % P, r"""
!u v. (!i. i < %(k)d ==> zq_list_ok (u i) /\ zq_list_ok (v i))
      ==> TqVectorDot_%(k)d_%(name)s_Configuration_hol (zvec %(k)d u) (zvec %(k)d v) =
          Value (FIPS203_Poly
                  (zqlist (\n. ring_sum mlkem_zq {j | j < %(k)d}
                                (\j. fips203_multiply_ntts (zarr (u j)) (zarr (v j)) n))))""" % P)
    add(Q, "TQMATRIXVECTORMUL_%(k)d" % P, r"""
!a v. (!i j. i < %(k)d /\ j < %(k)d ==> zq_list_ok (a i j)) /\
      (!j. j < %(k)d ==> zq_list_ok (v j))
      ==> TqMatrixVectorMul_%(k)d_%(name)s_Configuration_hol (zmat %(k)d a) (zvec %(k)d v) =
          Value (zvec %(k)d
                  (\i. zqlist (\n. ring_sum mlkem_zq {j | j < %(k)d}
                                    (\j. fips203_multiply_ntts
                                          (zarr (a i j)) (zarr (v j)) n))))""" % P)
    add(Q, "TQMATRIXTRANSPOSEVECTORMUL_%(k)d" % P, r"""
!a v. (!i j. i < %(k)d /\ j < %(k)d ==> zq_list_ok (a i j)) /\
      (!j. j < %(k)d ==> zq_list_ok (v j))
      ==> TqMatrixTransposeVectorMul_%(k)d_%(name)s_Configuration_hol
            (zmat %(k)d a) (zvec %(k)d v) =
          Value (zvec %(k)d
                  (\i. zqlist (\n. ring_sum mlkem_zq {j | j < %(k)d}
                                    (\j. fips203_multiply_ntts
                                          (zarr (a j i)) (zarr (v j)) n))))""" % P)

# ---------------------------------------------------------------------------
# kpke.ml: K-PKE (FIPS 203 Algorithms 13, 14, 15)
# ---------------------------------------------------------------------------

for P in PARAMS:
    add("kpke", "KPKE_KEYGEN_%(NB)s_EQUIV" % P, r"""
!d. (!i j. i < %(k)d /\ j < %(k)d
           ==> sample_ok (APPEND (FST (mlkem_g (APPEND d [word %(k)d:byte])))
                                 [word j; word i]))
    ==> K_PKE_KeyGen_%(name)s_Configuration_hol d = Value (kpke_keygen %(p)s d)""" % P)
    add("kpke", "KPKE_ENCRYPT_%(NB)s_EQUIV" % P, r"""
!ek m r.
  LENGTH ek = %(EK)d /\ LENGTH m = 32 /\
  (!i j. i < %(k)d /\ j < %(k)d
         ==> sample_ok (APPEND (mlkem_slice %(T)d 32 ek) [word j; word i]))
  ==> K_PKE_Encrypt_%(name)s_Configuration_hol ek m r =
      Value (kpke_encrypt %(p)s ek m r)""" % P)
    add("kpke", "KPKE_DECRYPT_%(NB)s_EQUIV" % P, r"""
!dk c.
  LENGTH dk = %(T)d /\ LENGTH c = %(C)d
  ==> K_PKE_Decrypt_%(name)s_Configuration_hol dk c =
      Value (kpke_decrypt %(p)s dk c)""" % P)

# ---------------------------------------------------------------------------
# mlkem.ml: ML-KEM (FIPS 203 Algorithms 16-21) and the input checks
# ---------------------------------------------------------------------------

for P in PARAMS:
    keyhyp = (r"(!i j. i < %(k)d /\ j < %(k)d ==> sample_ok (APPEND (FST (mlkem_g "
              r"(APPEND d [word %(k)d:byte]))) [word j; word i]))") % P
    ekhyp = (r"(!i j. i < %(k)d /\ j < %(k)d ==> sample_ok (APPEND (mlkem_slice "
             r"%(T)d 32 ek) [word j; word i]))") % P
    dkhyp = (r"(!i j. i < %(k)d /\ j < %(k)d ==> sample_ok (APPEND (mlkem_slice "
             r"%(RHO_DK)d 32 dk) [word j; word i]))") % P
    P2 = dict(P, keyhyp=keyhyp, ekhyp=ekhyp, dkhyp=dkhyp)
    add("mlkem", "MLKEM_KEYGEN_INTERNAL_%(NB)s_EQUIV" % P, r"""
!d z. %(keyhyp)s
      ==> ML_KEM_KeyGen_internal_%(name)s_Configuration_hol d z =
          Value (mlkem_keygen_internal %(p)s d z)""" % P2)
    add("mlkem", "MLKEM_ENCAPS_INTERNAL_%(NB)s_EQUIV" % P, r"""
!ek m. LENGTH ek = %(EK)d /\ LENGTH m = 32 /\ %(ekhyp)s
       ==> ML_KEM_Encaps_internal_%(name)s_Configuration_hol ek m =
           Value (mlkem_encaps_internal %(p)s ek m)""" % P2)
    add("mlkem", "MLKEM_DECAPS_INTERNAL_%(NB)s_EQUIV" % P, r"""
!dk c. LENGTH dk = %(DK)d /\ LENGTH c = %(C)d /\ %(dkhyp)s
       ==> ML_KEM_Decaps_internal_%(name)s_Configuration_hol dk c =
           Value (mlkem_decaps_internal %(p)s dk c)""" % P2)
    add("mlkem", "MLKEM_EK_CHECK_%(NB)s_EQUIV" % P, r"""
!ek. ML_KEM_EncapsKeyCheck_%(name)s_Configuration_hol ek =
     Value (mlkem_ek_check %(p)s ek)""" % P2)
    add("mlkem", "MLKEM_DECAPS_CHECK_%(NB)s_EQUIV" % P, r"""
!dk c. ML_KEM_DecapsInputCheck_%(name)s_Configuration_hol dk c =
       Value (mlkem_decaps_check %(p)s dk c)""" % P2)
    add("mlkem", "MLKEM_KEYGEN_%(NB)s_EQUIV" % P, r"""
!ent d z. ent 0 = SOME d /\ ent 1 = SOME z /\ %(keyhyp)s
          ==> ML_KEM_KeyGen_%(name)s_Configuration_hol ent =
              Value (Native_Value (mlkem_keygen_internal %(p)s d z))""" % P2)
    add("mlkem", "MLKEM_KEYGEN_%(NB)s_BOTTOM" % P, r"""
!ent. ent 0 = NONE \/ ent 1 = NONE
      ==> ML_KEM_KeyGen_%(name)s_Configuration_hol ent = Value Native_Bottom""" % P2)
    add("mlkem", "MLKEM_ENCAPS_%(NB)s_EQUIV" % P, r"""
!ent ek m kc. ent 0 = SOME m /\ LENGTH m = 32 /\ %(ekhyp)s /\
              mlkem_encaps_checked %(p)s ek m = SOME kc
              ==> ML_KEM_Encaps_%(name)s_Configuration_hol ent ek =
                  Value (Native_Value kc)""" % P2)
    add("mlkem", "MLKEM_ENCAPS_%(NB)s_BOTTOM" % P, r"""
!ent ek. ent 0 = NONE
         ==> ML_KEM_Encaps_%(name)s_Configuration_hol ent ek = Value Native_Bottom""" % P2)
    add("mlkem", "MLKEM_DECAPS_%(NB)s_EQUIV" % P, r"""
!dk c kk. mlkem_decaps_checked %(p)s dk c = SOME kk /\ %(dkhyp)s
          ==> ML_KEM_Decaps_%(name)s_Configuration_hol dk c = Value kk""" % P2)


# ---------------------------------------------------------------------------
# final.ml: the same statements as above without the sample_ok hypotheses
# ---------------------------------------------------------------------------

for P in PARAMS:
    add("final", "KPKE_KEYGEN_%(NB)s_FINAL" % P, r"""
!d. K_PKE_KeyGen_%(name)s_Configuration_hol d = Value (kpke_keygen %(p)s d)""" % P)
    add("final", "KPKE_ENCRYPT_%(NB)s_FINAL" % P, r"""
!ek m r.
  LENGTH ek = %(EK)d /\ LENGTH m = 32
  ==> K_PKE_Encrypt_%(name)s_Configuration_hol ek m r =
      Value (kpke_encrypt %(p)s ek m r)""" % P)
    add("final", "MLKEM_KEYGEN_INTERNAL_%(NB)s_FINAL" % P, r"""
!d z. ML_KEM_KeyGen_internal_%(name)s_Configuration_hol d z =
      Value (mlkem_keygen_internal %(p)s d z)""" % P)
    add("final", "MLKEM_ENCAPS_INTERNAL_%(NB)s_FINAL" % P, r"""
!ek m. LENGTH ek = %(EK)d /\ LENGTH m = 32
       ==> ML_KEM_Encaps_internal_%(name)s_Configuration_hol ek m =
           Value (mlkem_encaps_internal %(p)s ek m)""" % P)
    add("final", "MLKEM_DECAPS_INTERNAL_%(NB)s_FINAL" % P, r"""
!dk c. LENGTH dk = %(DK)d /\ LENGTH c = %(C)d
       ==> ML_KEM_Decaps_internal_%(name)s_Configuration_hol dk c =
           Value (mlkem_decaps_internal %(p)s dk c)""" % P)
    add("final", "MLKEM_KEYGEN_%(NB)s_FINAL" % P, r"""
!ent d z. ent 0 = SOME d /\ ent 1 = SOME z
          ==> ML_KEM_KeyGen_%(name)s_Configuration_hol ent =
              Value (Native_Value (mlkem_keygen_internal %(p)s d z))""" % P)
    add("final", "MLKEM_ENCAPS_%(NB)s_FINAL" % P, r"""
!ent ek m kc. ent 0 = SOME m /\ LENGTH m = 32 /\
              mlkem_encaps_checked %(p)s ek m = SOME kc
              ==> ML_KEM_Encaps_%(name)s_Configuration_hol ent ek =
                  Value (Native_Value kc)""" % P)
    add("final", "MLKEM_DECAPS_%(NB)s_FINAL" % P, r"""
!dk c kk. mlkem_decaps_checked %(p)s dk c = SOME kk
          ==> ML_KEM_Decaps_%(name)s_Configuration_hol dk c = Value kk""" % P)


# Two-sided versions of Encaps and Decaps. The generated Encaps and Decaps do
# not run the input check of FIPS 203 sections 7.2 and 7.3; the generated model
# has the checks as separate functions. The handwritten
# mlkem_encaps_checked and mlkem_decaps_checked are defined as "if the check
# passes then SOME _ else NONE". So the faithful statement is: when the generated check passes, the two agree in
# both directions; when it fails, the handwritten function returns NONE.
for P in PARAMS:
    add("final", "MLKEM_ENCAPS_%(NB)s_AGREE" % P, r"""
!ent ek m kc.
  ent 0 = SOME m /\ LENGTH m = 32 /\
  ML_KEM_EncapsKeyCheck_%(name)s_Configuration_hol ek = Value T
  ==> (ML_KEM_Encaps_%(name)s_Configuration_hol ent ek =
       Value (Native_Value kc) <=>
       mlkem_encaps_checked %(p)s ek m = SOME kc)""" % P)
    add("final", "MLKEM_ENCAPS_%(NB)s_REJECT" % P, r"""
!ek m. ML_KEM_EncapsKeyCheck_%(name)s_Configuration_hol ek = Value F
       ==> mlkem_encaps_checked %(p)s ek m = NONE""" % P)
    add("final", "MLKEM_DECAPS_%(NB)s_AGREE" % P, r"""
!dk c kk.
  ML_KEM_DecapsInputCheck_%(name)s_Configuration_hol dk c = Value T
  ==> (ML_KEM_Decaps_%(name)s_Configuration_hol dk c = Value kk <=>
       mlkem_decaps_checked %(p)s dk c = SOME kk)""" % P)
    add("final", "MLKEM_DECAPS_%(NB)s_REJECT" % P, r"""
!dk c. ML_KEM_DecapsInputCheck_%(name)s_Configuration_hol dk c = Value F
       ==> mlkem_decaps_checked %(p)s dk c = NONE""" % P)

# ---------------------------------------------------------------------------

OWNER_FILE = {
    "foundation": "foundation.ml", "bytes": "bytes.ml", "rq": "rq.ml",
    "ntt": "ntt.ml", "nttinv": "nttinv.ml", "sample": "sample_ntt.ml",
    "tq": "tq.ml", "kpke": "kpke.ml", "mlkem": "mlkem.ml",
    "final": "final.ml",
}

HEADER = """(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* Generated by tools/gen_interface.py; do not edit. *)
"""


def indent(s, n):
    pad = " " * n
    return "\n".join(pad + line if line else line for line in s.split("\n"))


def is_result(name):
    """The statements that carry the claim: the ML-KEM functions, unconditional."""
    import re
    if re.fullmatch(r"MLKEM_(ENCAPS|DECAPS)_(512|768|1024)_FINAL", name):
        return False        # one-way forms, superseded by _AGREE and _REJECT
    return bool(re.fullmatch(
        r"MLKEM_(KEYGEN|ENCAPS|DECAPS)_(INTERNAL_)?(512|768|1024)_FINAL"
        r"|MLKEM_(ENCAPS|DECAPS)_(512|768|1024)_(AGREE|REJECT)"
        r"|MLKEM_(EK|DECAPS)_CHECK_(512|768|1024)_EQUIV", name))


def statements_banner():
    W = 81

    def box(text=""):
        """One line of the banner, wrapped to the box width if necessary."""
        import textwrap
        indent = " " * (len(text) - len(text.lstrip()))
        pieces = textwrap.wrap(text, width=W - 6, subsequent_indent=indent + "  ") or [""]
        return "\n".join(("(* " + t).ljust(W - 2) + "*)" for t in pieces)

    rule = "(* " + "=" * (W - 6) + " *)"
    text = [
        "The statements of the equivalence between the FIPS 203 model generated by",
        "the FIPS pseudocode compiler and the handwritten model",
        "(common/fips203/fips203.ml).",
        "",
        "For the right input lengths, the generated ML-KEM function returns Value of",
        "what the handwritten function computes. The proofs and their tools are in",
        "core/; none of the statements below mentions anything from there.",
        "",
        "Parameter sets (FIPS 203 Table 2) and byte lengths:",
    ]
    for P in PARAMS:
        text.append("  ML-KEM-%s k=%d eta1=%d eta2=%d du=%d dv=%d  |ek|=%d |dk|=%d |c|=%d"
                    % ((P["NB"] + ":").ljust(5), P["k"], P["eta1"], P["eta2"],
                       P["du"], P["dv"], P["EK"], P["DK"], P["C"]))
    text += [
        "",
        "Reading the statements:",
        " - Value x is the success result of the generated (monadic) functions.",
        " - ent is the entropy oracle of the generated KeyGen and Encaps: ent n is",
        "   the n-th request for random bytes (ent 0 the first, ent 1 the second).",
        "   The statements assume that it returns the seeds that the handwritten",
        "   function is given. Native_Value x wraps a function result; the",
        "   generated function returns Native_Bottom instead if the random",
        "   generator fails, which has no counterpart in the handwritten model.",
        " - The handwritten mlkem_encaps_checked and mlkem_decaps_checked",
        "   return SOME _ when the input passes the check of FIPS 203 section",
        "   7.2 (7.3) and NONE when it does not; kc is the pair (shared key,",
        "   ciphertext) and kk the shared key.",
        "   The generated Encaps and Decaps do not run the check; the generated",
        "   model has the checks as separate functions, which are related to the",
        "   handwritten ones by the two check statements. So: when the generated",
        "   check passes, the generated function returns a result exactly when the",
        "   handwritten one returns SOME of it (_AGREE); when the generated check",
        "   fails, the handwritten function returns NONE (_REJECT).",
        " - Inputs of the wrong length are not covered.",
    ]
    return "\n" + "\n".join([rule] + [box(t) for t in text] + [rule]) + "\n"


RESULT_COMMENTS = {
    "KEYGEN": "KeyGen: if the oracle returns the seeds d and z, the generated function returns what mlkem_keygen_internal computes.",
    "ENCAPS_AGREE": "Encaps: if the generated key check passes, the generated function returns kc exactly when mlkem_encaps_checked returns SOME kc.",
    "ENCAPS_REJECT": "Encaps: if the generated key check fails, mlkem_encaps_checked returns NONE.",
    "DECAPS_AGREE": "Decaps: if the generated input check passes, the generated function returns kk exactly when mlkem_decaps_checked returns SOME kk.",
    "DECAPS_REJECT": "Decaps: if the generated input check fails, mlkem_decaps_checked returns NONE.",
    "KEYGEN_INTERNAL": "KeyGen_internal (FIPS 203 Algorithm 16): the seeds are arguments.",
    "ENCAPS_INTERNAL": "Encaps_internal (Algorithm 17): the message is an argument.",
    "DECAPS_INTERNAL": "Decaps_internal (Algorithm 18).",
    "EK_CHECK": "The encapsulation key check of FIPS 203 section 7.2.",
    "DECAPS_CHECK": "The decapsulation input check of FIPS 203 section 7.3.",
}


def result_kind(name, nb):
    for kind, fmt in [("KEYGEN_INTERNAL", "MLKEM_KEYGEN_INTERNAL_%s_FINAL"),
                      ("ENCAPS_INTERNAL", "MLKEM_ENCAPS_INTERNAL_%s_FINAL"),
                      ("DECAPS_INTERNAL", "MLKEM_DECAPS_INTERNAL_%s_FINAL"),
                      ("KEYGEN", "MLKEM_KEYGEN_%s_FINAL"),
                      ("ENCAPS_AGREE", "MLKEM_ENCAPS_%s_AGREE"),
                      ("ENCAPS_REJECT", "MLKEM_ENCAPS_%s_REJECT"),
                      ("DECAPS_AGREE", "MLKEM_DECAPS_%s_AGREE"),
                      ("DECAPS_REJECT", "MLKEM_DECAPS_%s_REJECT"),
                      ("EK_CHECK", "MLKEM_EK_CHECK_%s_EQUIV"),
                      ("DECAPS_CHECK", "MLKEM_DECAPS_CHECK_%s_EQUIV")]:
        if name == fmt % nb:
            return kind
    return None


def write_statements(fh):
    fh.write("(*\n * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.\n"
             " * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0\n *)\n\n"
             "(* Generated by common/fips203/generated/core/tools/gen_interface.py;      *)\n(* do not edit.                                                               *)\n")
    fh.write(statements_banner())
    stmts = {e[0]: e[2] for e in ENTRIES}
    order = ["KEYGEN", "ENCAPS_AGREE", "ENCAPS_REJECT", "DECAPS_AGREE",
             "DECAPS_REJECT", "KEYGEN_INTERNAL", "ENCAPS_INTERNAL",
             "DECAPS_INTERNAL", "EK_CHECK", "DECAPS_CHECK"]
    names = []
    import textwrap
    for P in PARAMS:
        fh.write("\n(* %s ML-KEM-%s %s *)\n" % ("-" * 20, P["NB"], "-" * 36))
        by_kind = {result_kind(n, P["NB"]): n for n in stmts if result_kind(n, P["NB"])}
        assert set(by_kind) == set(order), (P["NB"], set(order) - set(by_kind))
        for kind in order:
            n = by_kind[kind]
            names.append(n)
            fh.write("\n")
            for line in textwrap.wrap(RESULT_COMMENTS[kind], width=71):
                fh.write("(* %s *)\n" % line.ljust(71))
            fh.write("let %s_STMT = `\n%s`;;\n" % (n, indent(stmts[n], 1)))
    fh.write("\n(* The names of the statements above. *)\n")
    fh.write("let fips203_equiv_results = [\n")
    for n in names:
        fh.write('  "%s";\n' % n)
    fh.write("];;\n")
    assert sorted(names) == sorted(e[0] for e in ENTRIES if is_result(e[0]))


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    out = os.path.dirname(here)        # core/
    top = os.path.dirname(out)         # generated/, holds fips203_equivalence.ml
    names = [e[0] for e in ENTRIES]
    assert len(names) == len(set(names)), "duplicate names"

    with open(os.path.join(out, "interface.ml"), "w") as fh:
        fh.write(HEADER)
        fh.write("""
(* ========================================================================= *)
(* The statements that the proof files share. NAME_STMT is proved as NAME   *)
(* by the file named in the comment above it. Load after base.ml. The       *)
(* statements that carry the claim are not here but in                      *)
(* ../fips203_equivalence.ml,                                                *)
(* which this file loads.                                                    *)
(* ========================================================================= *)

loadt "common/fips203/generated/fips203_equivalence.ml";;

(* Left fold, which HOL Light's list library does not provide.              *)

let equiv_foldl = define
 `(!(g:I->S->S) s. equiv_foldl g s [] = s) /\\
  (!(g:I->S->S) s x l. equiv_foldl g s (CONS x l) = equiv_foldl g (g x s) l)`;;
""")
        cur = None
        for name, owner, stmt in ENTRIES:
            if is_result(name):
                continue
            if owner != cur:
                cur = owner
                fh.write("\n(* %s %s *)\n" % ("-" * 30, OWNER_FILE[owner]))
            fh.write("\nlet %s_STMT = `\n%s`;;\n" % (name, indent(stmt, 1)))
        fh.write("\nlet fips203_equiv_interface = [\n")
        for name, owner, _ in ENTRIES:
            fh.write('  "%s", "%s", %s_STMT;\n' % (name, OWNER_FILE[owner], name))
        fh.write("];;\n")

    with open(os.path.join(top, "fips203_equivalence.ml"), "w") as fh:
        write_statements(fh)

    with open(os.path.join(out, "stubs.ml"), "w") as fh:
        fh.write(HEADER)
        fh.write("""
(* DEVELOPMENT ONLY. Asserts every interface statement without proof so that *)
(* each proof file can be developed before the files it depends on are       *)
(* finished. all.ml never loads this file.                                   *)
""")
        for name, owner, _ in ENTRIES:
            fh.write("let %s = mk_thm([], %s_STMT);;\n" % (name, name))

    with open(os.path.join(out, "check.ml"), "w") as fh:
        fh.write(HEADER)
        fh.write("""
(* Check that every interface lemma is proved as stated, without hypotheses. *)

let fips203_equiv_check name th stmt =
  if hyp th <> [] then failwith (name ^ ": theorem has hypotheses")
  else if not (aconv (concl th) stmt) then
    failwith (name ^ ": theorem differs from the interface statement")
  else ();;

""")
        for name, owner, _ in ENTRIES:
            fh.write('fips203_equiv_check "%s" %s %s_STMT;;\n' % (name, name, name))
        fh.write("""
(* The kernel-level guard: mk_thm and new_axiom add to axioms(), so a theorem *)
(* asserted without proof anywhere in the loaded files would show up here.   *)
(* HOL Light itself has exactly three axioms.                                *)

let () =
  let ax = axioms () in
  print_endline ("FIPS203-EQUIV-AXIOMS " ^ string_of_int (length ax));
  List.iter (fun th -> print_endline ("  axiom: " ^ string_of_term (concl th))) ax;
  if length ax <> 3 then failwith "check: unexpected number of axioms";;

(* The RESULTS are monomorphic: no stray type variable in any of them.       *)

let () =
  List.iter
    (fun (name, _, stmt) ->
       if mem name fips203_equiv_results && type_vars_in_term stmt <> []
       then failwith (name ^ ": statement has type variables"))
    fips203_equiv_interface;;

""")
        fh.write('print_endline "FIPS203-EQUIV-RESULTS %d";;\n' % sum(1 for e in ENTRIES if is_result(e[0])))
        fh.write('print_endline "FIPS203-EQUIV-CHECK-PASSED %d lemmas";;\n' % len(ENTRIES))

    by_owner = {}
    for name, owner, _ in ENTRIES:
        by_owner.setdefault(owner, []).append(name)
    for owner, ns in by_owner.items():
        print("%-12s %3d  %s" % (owner, len(ns), OWNER_FILE[owner]))
    print("total        %3d" % len(ENTRIES))


if __name__ == "__main__":
    main()
