# Tests for the SHA-3 and ML-KEM specifications

This directory contains validation and testing material for the formal
specifications in `common/`:

 - `common/fips202.ml`: SHA-3 (FIPS 202)
 - `common/fips203.ml`: ML-KEM (FIPS 203)
 - `common/fips203_theory.ml`: properties of the ML-KEM specification,
   including the NTT-domain forms `KPKE_*_FIPS` of FIPS 203 Algorithms 13-15

## Files

 - `fips202_eval.ml`: conversions evaluating the FIPS 202 functions by proof.
 - `keccak_bridge.ml`: the theorem `KECCAK_F1600_BRIDGE` identifying
   `keccak_f1600` of `common/fips202.ml` with the lane-list `keccak 24` of
   `{arm,x86}/proofs/utils/keccak_spec.ml` (whose definitions are reproduced
   verbatim, so the files can be loaded together), and a faster evaluator of
   `keccak_f1600` based on it.
 - `fips202_test.ml`: standard SHA-3 test vectors as theorems.
 - `mlkem_eval.ml`: evaluation of the ML-KEM functions by proof
   (`MLKEM_EVAL_CONV`, `MLKEM_TOP_EVAL_CONV`), via the `KPKE_*_FIPS` theorems.
 - `mlkem_kat.ml`: known-answer tests on NIST ACVP vectors.
 - `vectors/*.ml`: the ACVP vectors used, as HOL terms.
 - `make_vectors.py`: generates `vectors/` from the ACVP JSON files.
 - `ref_mlkem.py`: a direct Python transcription of the HOL definitions in
   `common/fips203.ml`, used for fast (non-formal) cross-checking.
 - `check_acvp.py`, `check_keychecks.py`: run `ref_mlkem.py` on all the ACVP
   keyGen, encapsulation, decapsulation and key-check vectors.

## Running the HOL tests

From the root of the repository:

```
needs "common/fips203_theory.ml";;      (* spec and theory, about 10 seconds *)
needs "tests/mlkem/fips202_test.ml";;   (* SHA-3 test vectors, a few minutes *)
needs "tests/mlkem/mlkem_kat.ml";;
mlkem_kat "keygen512";;
```

`mlkem_kat id` returns a theorem such as
`|- mlkem_keygen_internal mlkem512 d z = (ek,dk)` with explicit byte lists
and prints whether the result matches the expected value. The tests are
named in `mlkem_kat_ids`: `keygenN`, `encapsN`, `decapsN_valid` and
`decapsN_reject` for N = 512, 768 and 1024, where the last two use a valid
ciphertext and an implicitly rejected one. Each takes from about 10 minutes
to over an hour, almost all of it evaluating Keccak, so `mlkem_kat_all()`
takes many hours, but the tests are independent and can be run in parallel
HOL sessions.

## Running the Python checks

These need the ACVP JSON files in a directory `ACVPDIR`, named
`keygen_prompt.json` and `keygen_expected.json` (`prompt.json` and
`expectedResults.json` from `gen-val/json-files/ML-KEM-keyGen-FIPS203` in
https://github.com/usnistgov/ACVP-Server), and `encdec_prompt.json` and
`encdec_expected.json` (the same from `ML-KEM-encapDecap-FIPS203`):

```
python3 -B tests/mlkem/check_acvp.py ACVPDIR 1000
python3 -B tests/mlkem/check_keychecks.py ACVPDIR
python3 -B tests/mlkem/make_vectors.py ACVPDIR tests/mlkem/vectors
```

The second argument of `check_acvp.py` limits the number of test cases used
from each test group. The vectors in `vectors/` were made from the files of
the ACVP-Server master branch as of 2026-10-25.

## Results

`check_acvp.py` and `check_keychecks.py` pass all 240 ACVP test cases (75
keyGen, 105 encapsulation/decapsulation, 60 key checks). All 12 HOL tests
pass. These are their CPU times when all 12 were run in parallel on one
machine (alone, `keygen512` takes about 700 seconds):

| Test          | ML-KEM-512 | ML-KEM-768 | ML-KEM-1024 |
|---------------|-----------:|-----------:|------------:|
| keygen        |     1536 s |     2388 s |      3132 s |
| encaps        |     1599 s |     2448 s |      3515 s |
| decaps_valid  |     1894 s |     3193 s |      4645 s |
| decaps_reject |     2023 s |     3078 s |      4765 s |

The ACVP test cases used are noted at the top of each file in `vectors/`.
