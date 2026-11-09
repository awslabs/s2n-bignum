# Tests for the ML-DSA specification

This directory contains validation material for the formal specification
of ML-DSA in `common/`:

 - `common/fips204.ml`: ML-DSA (FIPS 204)
 - `common/fips204_theory.ml`: properties of the ML-DSA specification,
   including the NTT-domain forms `MLDSA_*_FIPS` of FIPS 204 Algorithms
   6-8 and the equivalence with the alternative way of checking the low
   bits and computing the hints of Section 5.1 of the Round 3 Dilithium
   specification (`MLDSA_SIGN_ATTEMPT_ALT`, `MLDSA_SIGN_MU_ALT`)

## Files

 - `ref_mldsa.py`: a direct Python transcription of the HOL definitions in
   `common/fips204.ml`, used for fast (non-formal) cross-checking. It needs
   numpy, which it uses only for the products in R_q.
 - `check_acvp.py`: runs `ref_mldsa.py` on the ACVP keyGen, sigGen and
   sigVer vectors: the internal interface, with and without external mu,
   and the external one, pure ML-DSA with contexts and HashML-DSA with
   each of the pre-hash functions used by the vectors.

## Running the HOL theory

From the root of the repository:

```
needs "common/fips204_theory.ml";;
```

This takes about 7 minutes of CPU time, almost all of it loading
`Library/ringtheory.ml`.

## Running the Python checks

These need the directories `ML-DSA-keyGen-FIPS204`, `ML-DSA-sigGen-FIPS204`
and `ML-DSA-sigVer-FIPS204` from `gen-val/json-files` in
https://github.com/usnistgov/ACVP-Server, each with its `prompt.json` and
`expectedResults.json`, in a directory `ACVPDIR`:

```
python3 -B tests/mldsa/check_acvp.py ACVPDIR
```

An optional second argument limits the number of test cases used from each
test group.

## Results

`check_acvp.py` passes all 615 ACVP test cases (75 keyGen, 360 sigGen and
180 sigVer) of the files of the ACVP-Server master branch as of 2026-11-09.
