# RV32IM ML-DSA proof inputs

The assembly below is imported unchanged from mldsa-native pull request
1119 at commit
`20bc28eaffc0f02260aab7942c6e9bec002f184f`.

The local `src/common.h` is a proof-build adapter. It provides only the
preprocessor namespacing and ELF symbol directives used by the generated
assembly. Together with the flags in `riscv/Makefile`, it reproduces the
ML-DSA-44 objects built from the full upstream configuration.

The default NTT and inverse NTT objects use the additional low multiply in
the Barrett reduction. The `_slowmul` objects select the upstream shift/add
variant through `MLD_USE_NATIVE_RV32IM_SLOW_MULTIPLIER`. Both variants still
require `MULH`.

Constant-time use requires data-independent latency for `MUL` and `MULH` on
the selected RV32IM implementation.
