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
 - `mldsa_eval.ml`: evaluation of the ML-DSA functions by proof
   (`MLDSA_EVAL_CONV`, `MLDSA_TOP_EVAL_CONV`), via the NTT-domain forms
   `MLDSA_*_FIPS`. It uses the FIPS 202 evaluation of `tests/mlkem` with a
   faster Keccak-f[1600] and sponge (lanes as explicit chains of 64 bits,
   so that no large numerals are built), the NTT by a proved Cooley-Tukey
   splitting, the inverse NTT checked through `MLDSA_NTT_INV_UNIQUE`, and
   the rejection samplers through the accepted candidates.
 - `mldsa_kat.ml`: known-answer tests on NIST ACVP vectors.
 - `vectors/*.ml`: the ACVP vectors used, as HOL terms.
 - `make_vectors.py`: generates `vectors/` from the ACVP JSON files.

## Running the HOL theory

From the root of the repository:

```
needs "common/fips204_theory.ml";;
```

This takes about 7 minutes of CPU time, almost all of it loading
`Library/ringtheory.ml`.

## Running the HOL tests

From the root of the repository:

```
needs "tests/mldsa/mldsa_kat.ml";;
mldsa_kat "keygen44";;
```

`mldsa_kat id` returns a theorem such as
`|- mldsa_keygen_internal mldsa44 xi = (pk,sk)` with explicit byte lists
and prints whether the result matches the expected value. The tests are
named in `mldsa_kat_ids`: `keygenN`, `signN`, `verifyN_valid` and
`verifyN_reject` for N = 44, 65 and 87. The signing tests evaluate
`mldsa_sign_internal` (deterministic, with the formatted message M') to
`SOME sg`, with the attempts before the accepted one proved to be
rejected; the verification tests evaluate `mldsa_verify_internal` to `T`
or `F`. Loading `mldsa_kat.ml` (with `mldsa_eval.ml` and the files of
`tests/mlkem` that it uses) takes under a minute on top of
`common/fips204_theory.ml`. Each test takes from about 3 to 40 minutes of
CPU time and all 12 about 2.3 hours (see Results). `mldsa_kat_all()` runs
them all in one session, but the tests are independent and can be run in
parallel HOL sessions. The vectors are made by

```
python3 -B tests/mldsa/make_vectors.py ACVPDIR tests/mldsa/vectors
```

with `ACVPDIR` as for the Python checks below. The test cases used are noted
at the top of each file in `vectors/`.

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

All 12 HOL tests pass. These are their CPU times, in four fresh sessions
running at once on a shared machine with 16 virtual CPUs, each having
loaded `tests/mldsa/mldsa_kat.ml` (434 s) and then run some of the tests
one after another, so they are only a rough guide:

| Test          | ML-DSA-44 | ML-DSA-65 | ML-DSA-87 |
|---------------|----------:|----------:|----------:|
| keygen        |     175 s |     305 s |     511 s |
| sign          |    1029 s |    1261 s |    2294 s |
| verify_valid  |     290 s |     460 s |     809 s |
| verify_reject |     277 s |     234 s |     799 s |

The signing tests make 3 (ML-DSA-44) and 2 (ML-DSA-65, ML-DSA-87) signing
attempts. The accepted one takes most of the time, since all of its
coefficient checks and hints are evaluated, whereas a rejected attempt
stops at the first coefficient that fails a check. The rejected signatures
of the verification tests have a modified message (ML-DSA-44) or a
modified z (ML-DSA-87), both rejected only by the final comparison of the
challenge hashes, and a modified hint (ML-DSA-65), rejected by the hint
unpacking, so that this test is faster.
