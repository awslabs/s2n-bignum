# The compiler-generated FIPS 203 model

| File | Contents |
| --- | --- |
| [`fips203_generated.ml`](fips203_generated.ml) | The ML-KEM model that the FIPS pseudocode compiler generates from FIPS 203. It follows the pseudocode step by step. |
| [`fips203_equivalence.ml`](fips203_equivalence.ml) | The statements that this model computes what the handwritten model [`../fips203.ml`](../fips203.ml) computes, for ML-KEM-512, -768 and -1024: KeyGen, Encaps and Decaps, and the Encaps and Decaps input checks. |
| [`core/`](core/) | The proofs of these statements and the tools to check them. Start with [`core/README.md`](core/README.md). |

Read `fips203_equivalence.ml` for what is proved; nothing in it refers to
`core/`. To check the proofs, run `core/tools/check-all.sh`.

The two models differ in form. The handwritten model is deterministic, works
on lists of bytes, and has the random inputs of KeyGen and Encaps as
arguments (`mlkem_keygen_internal`, `mlkem_encaps_internal`; the `_checked`
variants add the input checks of FIPS 203 sections 7.2 and 7.3). The
generated model is monadic, reads its random inputs from an entropy oracle,
and has the input checks as separate functions. The statements relate the
two for every input of the right length.
