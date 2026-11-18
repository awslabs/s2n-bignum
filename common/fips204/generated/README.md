# The compiler-generated FIPS 204 model

| File | Contents |
| --- | --- |
| [`fips204_generated.ml`](fips204_generated.ml) | The ML-DSA model that the FIPS pseudocode compiler generates from FIPS 204. It follows the pseudocode step by step. |
| [`fips204_equivalence.ml`](fips204_equivalence.ml) | The statements that this model computes what the handwritten model [`../fips204.ml`](../fips204.ml) computes, for ML-DSA-44, -65 and -87: key generation, signing and verification, HashML-DSA, the internal algorithms and the length checks of the generated API. |
| [`core/`](core/) | The proofs of these statements and the tools to check them. Start with [`core/README.md`](core/README.md). |

Read `fips204_equivalence.ml` for what is proved; nothing in it refers to
`core/`. To check the proofs, load `core/all.ml` and then `core/check.ml`
from the repository root (see `core/README.md`).

The two models differ in form. The handwritten model is deterministic, works
on lists of bytes, and has the randomness of key generation and signing as
arguments (`mldsa_keygen_internal`, `mldsa_sign_internal`). The generated
model is monadic, reads its random inputs from an entropy oracle, hashes bit
strings through the uninterpreted `shake256_bits` and `shake128_bits` (the
statements assume that they are SHAKE256 and SHAKE128, `xof_ok`), and signs
in a loop that may not terminate. The handwritten signing functions take
a bound on the attempts of the loop (`NONE`, the search of FIPS 204, in all
statements) and return an `mldsa_sign_result` (`MLDSA_Sign_Success sg`,
`MLDSA_Sign_Error_BadContext` or `MLDSA_Sign_Error_OutOfAttempts`); the
verification functions return an `mldsa_verify_result`
(`MLDSA_Verify_Success`, `MLDSA_Verify_Error_InvalidSignature` or
`MLDSA_Verify_Error_BadContext`). The lifts `lift_sign_result`,
`lift_sign_internal_result`, `lift_verify_result` and `lift_verify_bool`
map them to the results of the generated functions.
