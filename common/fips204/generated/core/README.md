# FIPS 204: the generated specification equals the handwritten one

`common/fips204/generated/fips204_generated.ml` is the output of the FIPS pseudocode
compiler (HOL Light definitions of FIPS 204, monadic style).
`common/fips204/fips204.ml` is John Harrison's handwritten specification. This directory contains a HOL Light proof that
the two agree, for ML-DSA-44, -65 and -87.

## What is proved

The statements are in `../fips204_equivalence.ml`; `check.ml` checks that each
is the conclusion of the theorem proved here.

56 theorems, listed in `equivalence.ml` as `EQUIVALENCE_THEOREMS`, each
without hypotheses and quantified over all arguments. For each parameter
set they relate one generated function to the handwritten one:

| Generated function (suffix `_P_Configuration_hol`) | Handwritten |
|---|---|
| `ML_DSA_KeyGen` | `mldsa_keygen` |
| `ML_DSA_Sign`, `ML_DSA_Verify` | `mldsa_sign`, `mldsa_verify` |
| `ML_DSA_Verify_internal` | `mldsa_verify_internal` |
| `HashML_DSA_Sign`, `HashML_DSA_Verify` | `hash_mldsa_sign`, `hash_mldsa_verify` |
| `MLDSAVerifyPublic`, `HashMLDSASignPublic`, `HashMLDSAVerifyPublic`, `MLDSASignMuChecked`, `MLDSAVerifyMuChecked`, `MLDSAVerifyInternalChecked`, `MLDSAVerifyLengthCheck`, `PreHashAllowed` | the same functions behind the length and pre-hash checks of the generated API |

plus `EQ_PREHASH` and `EQ_OIDBYTES` (both parameter-independent). That is
44 theorems. The list also contains the internal algorithms
`ML_DSA_KeyGen_internal`, `ML_DSA_Sign_internal`, `ML_DSA_Sign_internal_mu`
and `ML_DSA_Verify_internal_mu` (proved in `keygen.ml`, `sign.ml`
and `verify.ml`), 12 theorems, which makes 56. The files also prove the
equivalence of every helper that these use (sampling, NTT, rounding,
encodings).

Example, ML-DSA-44 signing (`EQ_ML_DSA_SIGN_MLDSA44`):

    !ent sk m ctx rnd.
      xof_ok /\ LENGTH sk = 2560 /\ ent 0 = SOME rnd
      ==> ML_DSA_Sign_MLDSA44_Configuration_hol ent sk (bits_of_bytes m) ctx =
          lift_sign_result (mldsa_sign mldsa44 NONE sk m ctx rnd)

`ent` is the generated source of random bytes; as for ML-KEM, the
statements assume that the random generator does not fail: its first
output is `rnd`, the signing randomness. The second argument of `mldsa_sign`
is the bound on the attempts of the signing loop; `NONE` is the unbounded
search of FIPS 204, the only case that the generated model has. `mldsa_sign`
returns an `mldsa_sign_result`: `MLDSA_Sign_Success sg`,
`MLDSA_Sign_Error_BadContext` (a context of more than 255 bytes) or
`MLDSA_Sign_Error_OutOfAttempts` (no attempt of the signing loop is
accepted). `lift_sign_result` (`common.ml`) maps these to `Value
(Native_Value sg)`, `Value Native_Bottom` and `Nontermination`, the results
of the generated function. `mldsa_verify` returns an `mldsa_verify_result`
(`MLDSA_Verify_Success`, `MLDSA_Verify_Error_InvalidSignature`,
`MLDSA_Verify_Error_BadContext`), which `lift_verify_result` maps to `Value
(Native_Value T)`, `Value (Native_Value F)` and `Value Native_Bottom`. The
internal and checked functions without a native bottom use
`lift_sign_internal_result` (a signature is `Value sg`, `OutOfAttempts` is
`Nontermination`) and `lift_verify_bool` (`Value T` or `Value F`). The
handwritten `hash_mldsa_verify` and the functions that call it return
`MLDSA_Verify_Error_BadContext` for a context of more than 255 bytes, which
`HashML_DSA_Verify` reports as `Value F`.

## Assumptions

- `xof_ok` (`common.ml`): the generated file declares `shake256_bits`
  and `shake128_bits` as uninterpreted functions; `xof_ok` says that on
  `bits_of_bytes s` they are `shake256 s` and `shake128 s` of
  `common/fips202/fips202.ml`.
- Messages are `bits_of_bytes m` for a byte string `m`. Public keys,
  secret keys and signatures have the exact length of the parameter set
  (e.g. 1312, 2560, 2420 bytes for ML-DSA-44). The random
  generator does not fail: KeyGen, Sign, HashML-DSA.Sign and
  `HashMLDSASignPublic` assume `ent 0 = SOME` of the random bytes, which
  KeyGen requires to have 32 bytes; signing puts no length condition on
  the randomness. Failure of the generator (the generated function
  returns `Native_Bottom`) has no counterpart in the handwritten model
  and is not covered.
- The pre-hash functions (SHA-2, SHA-3 and the SHAKE variants of
  HashML-DSA) go through the uninterpreted `prehash_bits`; the handwritten
  `hash_mldsa_*` take the digest as an argument and the theorems pass
  `top_prehash n M` (`toplevel.ml`).
- `Native_Bottom` is the FIPS bottom (`MLDSA_Sign_Error_BadContext` and
  `MLDSA_Verify_Error_BadContext` of the handwritten model).
  `Nontermination` of the generated signing loop corresponds to
  `MLDSA_Sign_Error_OutOfAttempts` of the handwritten functions with
  bound `NONE`.

## Not covered

- Messages that are not a whole number of bytes (except the HashML-DSA
  pre-hash, which takes any bit string).
- That `common/fips204/fips204.ml` agrees with the FIPS 204 text. (The generated
  file is derived from the pseudocode by the compiler; this proof ties
  the two together, so a mistake would have to occur in both.)
- Termination probabilities of the signing loop; side channels.
- The relation to the mldsa-native code: those proofs are in
  `arm/proofs/mldsa_native` and `x86/proofs/mldsa_native` and are about
  machine code.

## What you have to trust

- HOL Light's kernel and its three axioms (infinity, choice, eta).
  `mk_thm`, `new_axiom` and `CHEAT_TAC` do not occur in this directory
  (checked by `check.ml`).
- The generated files `common/fips204/generated/fips204_generated.ml`
  (generated as `fips204.ml`), `core/compiler/fips204_obligations.ml` and
  `core/compiler/fips_hol_prelude.ml` are the compiler output; their SHA-256
  are in `core/compiler/README.md` and are checked by `check.ml`.
  `fips_hol_prelude.ml` is handwritten (the `isa_*` helpers).
- The definitions that occur in the 56 statements and are made here:
  `xof_ok`, `lift_sign_result`, `lift_sign_internal_result`,
  `lift_verify_result` and `lift_verify_bool` (`common.ml`) and
  `top_prehash` (`toplevel.ml`). The lifts
  `lift_zq`, `lift_poly`, `lift_intpoly`, `lift_bitpoly`, `lift_vec`,
  `lift_mat` (`common.ml`), `round_infnorm` (`rounding.ml`) and the
  `ntt_*`, `enc_*`, `hints_*` definitions appear only in intermediate
  lemmas. `check.ml` prints all constants added by these files.
- Three new constants of the generated file occur in the statements
  through the generated definitions: `shake256_bits`, `shake128_bits`,
  `prehash_bits`; none has an axiom.

## Notes for maintainers

- The proofs refer to names that the compiler generates (record fields,
  temporaries such as `callable_3_0`). They are pinned to the output of the
  compiler revision `0fb8bfd59` (see `common/fips204/generated/core/compiler/README.md`); a
  regenerated `fips204.ml` will need the proofs to be revisited.
- Generic lemmas about the generated monad live in `core.ml` and are used by
  all other files. A few proof generators and tactics are still local to one
  file (for example the BytesToBits generator in `ball.ml` and the BitPack
  generator in `encode.ml`).
- Loading is order-dependent only in the sense of the `needs` lines; loading
  `equivalence.ml` a second time in a session that already has it fails
  (constants are declared once).

## Check it

From the repository root, in HOL Light (about 25 min, about 1.5 GB):

    loadt "common/fips204/generated/core/all.ml";;
    (* expected last line: 56 theorems, 0 open hypotheses *)
    loadt "common/fips204/generated/core/check.ml";;

`check.ml` prints the axioms, the 56 statements with their hypothesis
counts, the new constants, the grep for escape hatches and the SHA-256
check. Its expected output is described in the header of `check.ml`.

## Files

Loading order (also the `needs` order of `equivalence.ml`):

| File | Content |
|---|---|
| `base.ml` | loads the generated and the handwritten specification |
| `common.ml` | the lifts from handwritten to generated values, and `xof_ok` |
| `core.ml` | generic facts about the generated monad, loops, residues, the XOF model; all other files use these instead of local copies |
| `rounding.ml` | Power2Round, Decompose, High/LowBits, MakeHint, UseHint, norms |
| `sample.ml` | RejNTTPoly, RejBoundedPoly, ExpandA, ExpandS |
| `ball.ml` | SampleInBall, ExpandMask, BytesToBits generators |
| `encode.ml` | bit and byte conversions, BitPack/BitUnpack, pk/sk/w1 encodings |
| `hints.ml` | HintBitPack/Unpack, CountOnes, sigEncode/sigDecode (given BitPack/BitUnpack) |
| `ntt.ml` | BitRev8, NTT, NTTInv on one polynomial |
| `ntt_vec.ml` | the vector and matrix functions of the NTT domain |
| `callables.ml` | the local helper functions inside Sign and Verify |
| `sigcodec.ml` | discharges the BitPack/BitUnpack hypotheses of `hints.ml` and `callables.ml` |
| `toplevel.ml` | the statements (templates), the wrappers, abstract lemmas for KeyGen and Verify |
| `keygen.ml`, `verify.ml`, `sign.ml` | the proofs of the internal algorithms from the components |
| `equivalence.ml` | discharges the remaining hypotheses and lists the 56 theorems |
| `all.ml`, `check.ml` | load everything; audit script |

Every component file loads on its own after `base.ml`, `common.ml` and
the files it `needs`. Rough load times on the reference machine: specs
17 min, `core.ml` 5 s, `ntt.ml` 1 min, `sign.ml` 1.5 min, the rest a few
seconds to 20 s each.
