# Contributing

How to keep the comparison complete when s2n-bignum gains an
instruction model. The terms (form, suite, family, entry, root) are in
the [README](README.md#terms). The commands, logs and the refresh
procedure are in [ci/README.md](ci/README.md).

## When s2n-bignum gains an instruction model

For a new Arm definition `arm_FOO`, CI reports "aarch64 public
instruction inventory differs; missing ['arm_FOO']". To cover it:

1. Find the Sail function that executes the instruction, and add an
   entry for each form to the table in [backend/arm.ml](backend/arm.ml):
   the call with the fixed arguments that select the form, and the
   register fields in the order s2n-bignum's decoder passes them.
2. List the instruction and its forms in a family of `ARM_FAMILIES` in
   [coverage.py](scripts/coverage.py). A new family is a new suite, with
   its own `generated/arm-<family>.ml`, `proofs/arm-<family>.ml` and
   `statements/arm-<family>.txt`.
3. Run `build.sh` and `run.sh arm <family>`, and read the new root and
   the run's `.context` in `_build/`. If the Sail body reaches something
   the exporter does not translate, the run stops; an interpretation for
   it is a `contracts` row in the table with its case in the translator,
   which records the Sail call and its HOL term for the report
   (`record_value` or `record_update`), and a row in
   [Interpretations](backend/README.md#interpretations).
4. Add the theorem to the suite's driver in `proofs/`, and run
   `check-proof.sh arm-<family>` on the model in `_build/` until it
   passes.
5. Regenerate `generated/`, run the proof check and record the new
   statements, as in [Refreshing the checked-in
   files](ci/README.md#refreshing-the-checked-in-files). Update the
   counts that tests and documents pin: the catalogue fingerprint in
   `tests/test_entry_catalogue.py`, the form counts in
   `tests/test_coverage.py` and `tests/test_ci.py`, the table under
   [What is proved](README.md#what-is-proved), the counts in
   [statements/README.md](statements/README.md#counts) and the
   [coverage map](docs/ARM-COVERAGE-MAP.md).

RV32 works the same way with [backend/rv32.ml](backend/rv32.ml), the
`RV32` table in coverage.py and `proofs/rv32.ml`. x86 uses the form
names in [backend/x86.ml](backend/x86.ml), entries in
[backend/x86_shina.ml](backend/x86_shina.ml) and
[backend/x86_rems.ml](backend/x86_rems.ml),
[x86_forms.py](scripts/x86_forms.py) and the x86 drivers in `proofs/`.

## Changing the translator

[backend/README.md](backend/README.md) describes the translator, its
checks and its tests. After a change that alters the output, refresh
`generated/` and review the diff, as in
[ci/README.md](ci/README.md#refreshing-the-checked-in-files).
