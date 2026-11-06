# Sail-to-HOL compiler guide

The backend is a plugin for the Sail compiler. It translates selected
Sail instruction bodies, and the helpers they call, into HOL Light
definitions that the proofs compare with s2n-bignum's instruction
relations. The translation is trusted: no theorem connects a generated
definition to the Sail code. This page describes how it works, so that it
can be reviewed. The [README](../README.md) gives the claims;
[TRUST.md](../TRUST.md) lists every interpretation the translator applies,
with its meaning and what it loses. x86 specifics are in
[docs/X86.md](../docs/X86.md).

## Sail concepts

Sail is a language for writing instruction set architectures. Its
compiler parses a model, resolves names and checks types, then calls the
plugin with the checked syntax tree, a type environment and effect
information. An **effect** is an operation such as a register write or a
throw; the translator uses effects to tell value calculations from
computations that change state.

A `val` declaration gives a function's type and preconditions; its
`function` definition gives the body. A **cut** keeps the declaration
and removes the body, and the translator supplies a HOL meaning instead.
Sail types can depend on numbers: `bits('N)` has length `'N`, and
`int('i)` is the single integer `'i`. Constraints such as
`0 <= 'i <= 31` belong to the type environment.

| libsail name | Meaning |
| --- | --- |
| `E_aux`, `P_aux`, `Typ_aux`, `DEF_aux` | wrappers around expression, pattern, type and top-level nodes, with source locations |
| `E_app`, `E_if`, `E_assign`, `E_return` | a call, conditional, assignment and return |
| `Type_check.tannot`, `typ_of`, `env_of` | the checked annotation of a node, and its type and scope |
| `id`, `kid` | program identifier, type-variable identifier |
| `nexp`, `n_constraint`, `KBindings` | numeric type expression, proposition about such expressions, map from type variables to instantiations |
| `effect_info` | the recorded effects of each function |

## Modules

[build.sh](../build.sh) compiles these modules against Sail's `libsail`
into `_build/sail_plugin_hol_light.cmxs`; [run.sh](../run.sh) loads the
plugin into Sail.

| Module | Responsibility |
| --- | --- |
| [entry.ml](entry.ml) | Entries: records that select one form (name, family, parameters, Sail call, result type, RV32 retirement flag); assumptions; supplied inputs (`input_lift`) |
| [arm.ml](arm.ml) | AArch64 entries, assumptions, cuts and the names interpreted without a cut |
| [rv32.ml](rv32.ml) | RV32IM entries, cuts, disabled extensions and interpreted names |
| [x86.ml](x86.ml) | x86 form names, widths and register fields shared by both x86 models; the state-binding kinds |
| [x86_shina.ml](x86_shina.ml) | shina scalar and VEX entries, assumptions and state bindings |
| [x86_rems.ml](x86_rems.ml) | REMS entries, assumptions, state bindings and checks of the loaded model |
| [sail_plugin_hol_light.ml](sail_plugin_hol_light.ml) | The translator: selection, translation, the cases of each interpretation, output |

The architecture-specific cases stay in the translator; each table file
lists, in a comment, the names it interprets and the case that does it.

## Pipeline

1. [run.sh](../run.sh) starts Sail on one model: the Arm inputs in the
   order of upstream's Makefile, the RISC-V project with
   [rv32.json](rv32.json) (32-bit registers, all 32 integer registers),
   shina's `x86.sail_project`, or the REMS inputs from its Makefile. Sail
   parses and typechecks the model before calling the plugin.
2. `prepare_upstream` first, for RV32, uses Sail's `split`
   transformation to give each instruction group of `execute` its own
   function, such as `execute_RTYPE`. It then selects the requested
   families' entries and any entries they call, has Sail typecheck them
   (`Entry.instantiate`), checks the assumptions against the model
   (`validate_assumptions`), and with `Callgraph.filter_ast_ids` keeps the
   functions the roots reach and removes the bodies of the cuts.
3. `export_checked` translates each root. A root is a **retirement
   relation** if its entry says so (RV32 branches and jumps, ECALL and
   EBREAK) or, for a root without an entry, with
   `--hol-light-normal-retirement`. Otherwise it is
   a **state computation** if it has effects or is an RV32 entry (PAUSE
   has none), and a pure function if not (only tests use pure roots). The state type comes from
   `--hol-light-architecture`: `armstate`, `riscvstate` or `x86state`
   (`armstate` when none is given).
4. `pure` and `tail` translate value expressions; `computation`
   translates state changes, mutable locals, loops and early returns,
   using continuations that say what to emit once a value is computed.
   `call` handles helper calls and primitives; `simple_write` and
   `flat_memory` handle register writes and memory accesses.
5. `lower_faults` turns the internal markers for faults, stops and
   rejections into HOL ([below](#relation-interface)), and `print_term`
   prints the term. Each definition is preceded by its Sail source.
6. With `--hol-light-output-dir`, the plugin translates every family
   before writing any file. `--hol-light-jobs N` translates families in up
   to N forked workers that start from the prepared state; their result
   files go to the output directory. `--hol-light-warmup STEM=N` first
   asks a family's z3 questions in N workers. Each model gets a dependency
   report, `<stem>.dependencies`
   ([generated/README.md](../generated/README.md#dependency-reports)).

The other options select what to translate (`--hol-light-family`,
`--hol-light-root`, `--hol-light-x86-source rems|shina`) and add
assumptions (`--hol-light-assume-feature`, `--hol-light-assume-bit`,
`--hol-light-assume-enum`, `--hol-light-assume-bool`). A run with entries
takes the assumptions of its table file and adds these.

## Relation interface

Every root that changes state exports a relation `R operands s t`. `s` is
the initial state and `t` a candidate final state. Helpers are expanded
or become shared definitions ([below](#sharing)); only roots are
relations.

| Reached in the source | Relation |
| --- | --- |
| normal end of a state computation | holds exactly when `t` is the computed state |
| normal end of a retirement relation (RV32 branches, jumps, ECALL, EBREAK) | holds when the result is `Retire_Success` and `t` is the computed state with an `EventJump` from the instruction's PC appended |
| Arm fault (`AArch64_SPAlignmentFault`, `throw(Error_Undefined())`) | holds for every `t` |
| `EndOfInstruction` | holds exactly when `t` is the state reached |
| false assertion, `exit()` | holds for no `t` |
| REMS throw | holds for no `t` |
| any other throw, fault or unsupported construct | generation stops |
| `undefined` | a fresh variable of its type, bound existentially around the relation; each evaluation chooses independently |

A fault is not a no-op: it skips the rest of the instruction. Neither
`EndOfInstruction` nor a generic `throw` counts as a fault, because Arm's
`EndOfInstruction` also ends normal executions, such as a constrained NOP.
During translation `Fault`, `Stop`, `Reject` and `Choose` are markers, not
HOL terms. `lower_faults` lowers them once the whole relation is built,
carrying early exits through `let` joins in sums so that the rest of the
instruction is emitted once. `print_term` refuses an unlowered marker, so
a shared helper that reached one fails to print rather than hide it.
A helper that can reach a fault, a throw, `EndOfInstruction` or an
`undefined` value, directly or through its callees, is expanded, never
shared.

An assertion is evaluated with its effects. If z3 proves it, the
dependency report records `statically-proved-assertion`; otherwise the
relation keeps it as a condition (`guarded-assertion`). A conditional
whose condition the translator decides keeps only the branch taken
(`statically-selected-branch`).

## Sharing

Without sharing, every call would be expanded into its root. Instead,
`shared_function_call` first tries to emit a called function once as a
`sail_hl_shared_...` definition:

1. It reads the parameters, their types and order from the checked Sail
   binding; there is no hand-written list.
2. It tries a polymorphic definition, with HOL type dimensions for the
   word widths (`Width policy: polymorphic` in the model).
3. If that fails, it fixes the numeric type variables that word types and
   loop bounds need to the caller's values. It starts with all of them
   and drops each one that the translation can do without, so the set has
   no removable choice, though it need not be the smallest
   (`Width policy: specialized`).
4. If neither works, the call is expanded in place. If a shared result
   loses a numeric fact that the caller needs later, the whole root is
   translated again without sharing.

Each failed attempt restores all bookkeeping (`translation_checkpoint`).
The report records chosen definitions as `shared-function` and failed
attempts as `specialization-required`. Retirement relations, recursive
calls and the helpers named under
[Relation interface](#relation-interface) are not shared.

Arguments are evaluated, in Sail's order, before the call. A shared
function that changes state returns its value and the new state, and also
receives the instruction's entry state `entry`, so that reads of the
instruction's PC see its value before any write. Facts the caller knows
about a call's result (constants, bounds, a known enum constructor)
travel beside the emitted call (`Shared_value`); they never replace the
call or drop its effects.

A shared definition claims to match Sail only on the source domain of its
parameters. Each concrete call still checks the callee's preconditions in
the caller's scope (`specialize_helper`).

The generated file ends by rebinding each root's OCaml name to a theorem
that the kernel derives from its definition by unfolding the shared
definitions and reducing numerals (`let ... = CONV_RULE ...`). The
constants are unchanged.

## Widths

- Sail `bits('N)` with `'N` fixed becomes `N word`; widths from 0 to 2,048
  bits are supported. A polymorphic width becomes a HOL type dimension
  such as `(N0)word`, and `2*'N` becomes `((N0)tybit0)word`, so that
  substituting `N0 = 32` gives exactly `64 word`. Other width
  expressions are specialized, never given an invented dimension.
- A shared definition's own widths are assumed positive; sharing is not
  tried when an argument can be an empty vector. Facts about a width are
  tied to the binding location of its type variable, so a helper inlined
  into the shared function, with its own `'N`, does not inherit them.
- Bitfield masks whose width comes from an immediate operand use an
  internal `Dynamic_bits` value: the width and an unsigned number. It
  supports zero, complement and extension to a fixed width, and cannot
  appear in a root parameter or a register.
- `slice` needs a proved in-bounds offset and an exact length.
  `set_slice_bits` on a partly assigned word needs a fixed offset.
- A word declared `undefined` keeps a mask of its assigned bits. A read or
  a final register write must use only assigned bits (`observable_value`).
  A branch or loop join keeps the masks of whole words only, so it refuses
  a tuple that holds a partly assigned word.
- Loops are expanded only with known bounds and a positive step: at most
  256 iterations per loop and 4,096 steps per root. Direct recursion is
  expanded while one numeric type argument shrinks and none grows, to
  depth 64, within the same budget. REMS adds recursion on integer values
  ([TRUST.md](../TRUST.md#interpretations)).

## Supplied inputs

Some x86 bodies fetch instruction bytes, such as a ModR/M byte or an
immediate, before computing. A **supplied input** replaces such a fetch by
a root parameter. An entry names the source function and the fetch with
`Entry.input_lift`, for example

```ocaml
Entry.input_lift ~fixed_arguments:["op", 23]
  "dispatch_vex_0f38_arith" "fetch"
```

which fixes `op = 23` (VPTEST) and turns its `fetch(1)` into a parameter.
`Entry.lifted_definitions` derives a new function from the checked body:
it replaces exactly the expected number of direct calls, each at its own
place, with fresh parameters ordered by source position, and Sail checks
the result and recomputes its effects. `~through:"fetch_modrm"` does the
same inside one helper, then redirects the caller's one call to the
derived helper.

A fixed argument selects the first matching case in source order: a
literal, a variable or a wildcard, with closed guards over integer
comparisons and pure Boolean operations. No instruction body, helper or
register is evaluated to choose a case. The derivation refuses a count
mismatch, calls inside loops, non-literal call arguments, unbound type
witnesses, recursive helper paths and name collisions. Each reached input
has a `source-input-boundary` record in the dependency report and a
`Source input boundary:` comment in the model.

## Names

- `symbol` keeps letters and digits and writes every other byte as `_`
  and two hex digits: `_` becomes `_5f` and `-` becomes `_2d`.
- A root is `sail_hl_` followed by its escaped entry name. Entry names are
  `ARM_...` in the carry, logical, AES, SHA2 and crypto-bitwise families,
  `arm_...` in the other AArch64 families, `rv_...` for RV32, `X86_...`
  for shina and `X86_REMS_...` for REMS. So the 64-bit ADC root is
  `sail_hl_ARM_5fADC64` and RV32 LW is `sail_hl_rv_5fLOAD_5fLW`.
- Shared definitions are `sail_hl_shared_<stem>_<name>_<index>`; Sail
  types and constructors become `sail_hl_type_...` and `sail_hl_ctor_...`;
  a Sail register `R` without an interpretation becomes a component
  parameter `reg_R`.
- REMS types, constructors and case functions carry the escaped output
  stem, as in `sail_hl_ctor_x86_2drems_2dshift_Mode_5f64bit`, so that both
  x86 models load into one kernel.
- [coverage.py](../scripts/coverage.py) and
  [x86_forms.py](../scripts/x86_forms.py) map each root to its theorem
  name ([statements/README.md](../statements/README.md#names)).

## Source references

Before every definition, the model names the Sail declarations and
bodies it came from, as `(* Sail source "<name>", "<path>:<line>" *)`,
read from Sail's source locations rather than rebuilt from the
translation. Checkout prefixes are replaced by stable model paths
([generated/README.md](../generated/README.md#source-checkouts)). For
functions that Sail generates, such as a bitfield's getters, the model
names the original declaration and says so. With
`--hol-light-quote-sources` the exporter also copies the source text into
the model, as OCaml quoted strings inside comments with a delimiter
absent from the text, so Sail text cannot end the comment; the checked-in
models are generated without it. Before a root the model also quotes its
table entry as "Selected Sail call", with the HOL parameter that holds
each field.

## What the translator checks or refuses

The translator stops generation rather than emit a construct it does not
support. It checks:

| Property | Example and implementation |
| --- | --- |
| Widths and preconditions | A helper returning `bits('N)` needs a valid HOL width. `specialize_helper` also checks the callee's numeric preconditions in the caller's scope; choosing a width alone is not enough. `prove_specialized` asks Sail's constraint solver |
| Evaluation order | In `F + write_then()`, the read of `F` comes before a helper that may write `F`. `computation_arguments` binds the read first |
| Scope and returns | A helper's early return resumes its caller; a block-local assignment does not overwrite a shadowed outer local (`restore_binding_scope`) |
| Initialization | See the masks under [Widths](#widths) |
| Branches and loops | Every exit contributes to a local's bounds; `computation_join` binds the joined state and locals once and emits the rest once |
| Interpretations | Each interpretation checks the declared signature, the types and the index bounds before it applies; an impure declaration never gets a pure primitive's meaning |
| Primitive widths | HOL's `word_zx` and `word_sx` truncate and `bit 0 x` reads any word; the cases of `call` check the operand and result widths each HOL operation requires |
| Bit order | Sail bit order is most significant first; `prepare_upstream` refuses a model without `default Order dec` |
| Strings | Literals print as `CONS (ASCII ...)` lists, so no byte can end a quotation |
| Enumerations | A match keeps its cases and one final wildcard, which must cover the rest |
| Small words | A match on a word of at most 4 bits needs exact literals; up to 8 bits, ordered masks; on a tuple of words of at most 8 bits in all, literals or wildcards, tested in order, that cover every value |

It refuses, among others:

- integer and refined Boolean root arguments, and dynamic widths in roots;
- a match binder named like a mutable local; type-variable patterns in
  match clauses; a match on a value with undefined bits; guarded word,
  Boolean and integer matches; a unit-variant wildcard (only a final
  variable is allowed);
- constraint expressions (`E_constraint`); `sizeof` of a shared
  function's numeric parameter;
- a fault, stop or rejection inside a sum-match arm, also under REMS;
- a control-flow join with no normal exit;
- a direct write to RV32's PC and writes that could change an assumed
  register or field;
- any architectural fault other than those in the
  [relation interface](#relation-interface).

A `let` that shadows a type variable drops the facts about it.

## Pitfalls covered by regression tests

Each of these would look plausible but lose a source effect or expose an
unassigned value; [test_backend.py](../tests/test_backend.py) covers both
the refusal and a valid control:

- A direct write to RV32's instruction PC must be refused: mapping it to
  an ordinary component while reads use the entry PC would lose it.
- A memory access kind must be the real `Load(Data)` or `Store(Data)`
  constructor; a helper named `Load` must not lose its effects.
- A stateless primitive needs a pure declaration: an impure `add_int`
  must not become HOL addition, and an impure `eq_bits` guard must not
  become HOL equality.
- Copying a tuple keeps which bits of its words are assigned.
- `X_set` and `V_set` capture index, width and value in Sail's order: in
  `X_set(unsigned(Selector), width(), changed(x))` the destination uses
  the old selector even if a later argument changes it.

## Source map

| Area | Entry points |
| --- | --- |
| Types and terms | `hol_type`, `type_text`, `print_term` |
| State and scope | the `context` type, `restore_binding_scope`, `register` |
| Helper calls | `specialize_helper_types`, `specialize_helper` |
| Sharing | `shared_function_call`, `translation_checkpoint` |
| Widths | `poly_dimension`, `numeric_type_term` |
| Source references | `source_comment`, `definition_source_comments` |
| Value checks | `observable_value`, `alias_value`, `insert_word`, `word_bounds` |
| Expressions and primitives | `pure`, `tail`, `call` |
| State updates | `computation`, `computation_arguments`, `computation_join`, `simple_write`, `flat_memory` |
| Control lowering | `lower_faults` |
| Roots and output | `prepare_upstream`, `export_checked`, `target` |

## Building and testing

The plugin must be built with the OCaml compiler and `libsail` that built
the Sail executable. [ci/setup.sh](../ci/setup.sh) builds both at the
pinned versions; [build.sh](../build.sh) is the only build of the plugin.
Set `SAIL_BUILD_DIR` for a separately built Sail. To export one family
and prove it:

```sh
bash tools/sail/build.sh
bash tools/sail/run.sh arm carry \
  --hol-light-output-dir "$PWD/tools/sail/_build"
bash tools/sail/check-proof.sh arm-carry
```

`check-proof.sh` does not audit the log; `ci/check.py proofs` does.

The tests:

- [test_backend.py](../tests/test_backend.py) runs the real Sail frontend
  and the plugin on small programs held in memory. It needs
  `SAIL_HOL_PLUGIN` and a `SAIL_BUILD_DIR` that contains Sail's
  `dune_site__Dune_site_data.cmx`, which installed `libsail` lacks.
- [test_selection.py](../tests/test_selection.py) checks that dependency
  selection keeps what a root uses, drops the rest and removes the bodies
  of cuts.
- [test_entry_catalogue.py](../tests/test_entry_catalogue.py) fixes every
  Arm entry (names, operand types, modes, Sail calls) in one fingerprint,
  with independent checks of aliases, field domains, operand order and
  selectors.
- [test_upstream_launcher.py](../tests/test_upstream_launcher.py) checks
  the input order and configuration of `run.sh`.

Tests and well-typed output do not replace review of the interpretations.
