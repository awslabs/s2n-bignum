# x86 divergences

This page records every known difference between a Sail x86 model and
s2n-bignum's relations in `x86/proofs/x86.ml`, for the register forms in
[x86_forms.py](../scripts/x86_forms.py). Each Sail model, shina or REMS
([X86.md](X86.md)), is compared with s2n-bignum only. Sail sources are
cited at the commits pinned in [ci/versions.env](../ci/versions.env); Intel
references are to the Software Developer's Manual, Volume 2B, order
253667-093US (September 2026).

Each difference is proved by a closed `_DIFF` theorem: an initial and a
final state that one relation permits and the other rejects
([statements/README.md](../statements/README.md#kinds)). A `_DIFF`
theorem does not say what the other relation permits instead. The REMS
witnesses compare the REMS root under `sail_hl_x86_core`, which resets
RIP. Their states are `sail_hl_x86_rems_diff_initial x s`, which sets
register 0 to `x` and clears CF and OF in an arbitrary state `s`, and
explicit writes over it.

"Permits more" below says which relation permits a superset of the
other's final states. This matters for s2n-bignum: a proof about
s2n-bignum code holds for every behaviour its relation permits, so where
s2n-bignum permits more, the difference cannot invalidate such a proof.
Where a Sail model permits a state that s2n-bignum rejects, a proof could
rely on behaviour that this model does not guarantee.

| Entry | Forms | Permits more | Evidence |
| --- | --- | --- | --- |
| [RCL/RCR full-cycle OF](#rcl-rcr-full-cycle-of) | shina RCL and RCR at 8, 8 legacy and 16 bits | s2n-bignum (proved) | `_EXACT` and `_DIFF` |
| [REMS ROR carry](#rems-ror-cf) | REMS ROR at every width | neither (source); s2n-bignum permits a state REMS rejects (proved) | a conjunct of each `_DIFF` |
| [REMS SAR carry](#rems-sar-cf) | REMS SAR at 8, 8 legacy and 16 bits | REMS (source); REMS permits a state s2n-bignum rejects (proved) | `_DIFF` |
| [REMS zero-count rotate OF](#rems-rotate-zero-of) | REMS ROL and ROR at every width | REMS (source); REMS permits a state s2n-bignum rejects (proved) | a conjunct of each `_DIFF` |
| [REMS wide rotate counts](#rems-rotate-wide-count) | REMS ROL, ROR, RCL and RCR at 8, 8 legacy and 16 bits | REMS permits states s2n-bignum rejects (proved); the converse is not proved | a conjunct of each `_DIFF` |

A REMS form with several findings has one `_DIFF` theorem with one
conjunct per finding, so the rows overlap.
No native x86 hardware measurement has been made for any entry.

## rcl-rcr-full-cycle-of

A carry rotate by a nonzero masked count can rotate the operand and CF by
a whole cycle: at masked counts 9, 18 and 27 for bytes and 17 for 16-bit
operands. The data and CF are then unchanged.

```text
initial:  AL = 0, CF = 0, OF = 0
RCL AL,9
shina:    AL = 0, CF = 0, OF = 0          (OF preserved)
s2n:      AL = 0, CF = 0, OF = 0 or 1     (OF undefined for count > 1)
```

shina restores OF when the effective count is zero
(`model/insn_groups.sail:452-454,475-477`). s2n-bignum's `x86_RCL` and
`x86_RCR` make OF undefined whenever the masked count exceeds one
(`x86/proofs/x86.ml:1483,1499`). Literal count zero preserves every flag
in both.

Permits more: s2n-bignum. The `_EXACT` theorems in
[x86-shift.ml](../proofs/x86-shift.ml) state, for every register, count
and state, that shina's relation is s2n-bignum's with OF also kept at the
whole-cycle counts. Each `_DIFF` follows from its `_EXACT`: at count 9
(17 at 16 bits), s2n-bignum permits flipping OF and shina does not.

Classification is open. Intel's pseudocode tests the masked count when
choosing undefined OF (pages 4-535/536); its prose says that a zero-bit
rotate changes no flags (pages 4-535/537). Neither model is changed.

## rems-ror-cf

REMS's ROR sets CF from the result's least significant bit for masked
counts above one, at every width (`ror_spec_8` at
`model/rotates_spec.sail:425` and the other widths after it, with
`rotate_right` in `model/prelude.sail:528`). Intel defines CF as the
result's most significant bit (page 4-536), as s2n-bignum does.

```text
initial:  AL = 0x04, CF = 0
ROR AL,2
REMS:     AL = 0x01, CF = 1
Intel:    AL = 0x01, CF = 0
s2n:      AL = 0x01, CF = 0               (bit 7 of the result)
```

Permits more: neither, by the source reading; REMS and s2n-bignum choose
different values of CF. The theorems prove one direction: one conjunct of
each `SAIL_HL_X86_REMS_ROR*_RI_DIFF` in
[x86-rems-shift.ml](../proofs/x86-rems-shift.ml) takes register 0 equal
to 4 and count 2, where s2n-bignum permits the final state with register
0 equal to 1 and CF and OF clear, and REMS rejects it.

## rems-sar-cf

REMS's 8- and 16-bit SAR mark CF undefined when the masked count is at
least the operand width (`model/shifts_spec.sail:431,480`). Intel fixes CF
to the last bit shifted out, which is then the sign bit (pages
4-605/606), as s2n-bignum does.

```text
initial:  AL = 0xff
SAR AL,8
REMS:     AL = 0xff, CF = 0 or 1
Intel:    AL = 0xff, CF = 1
s2n:      AL = 0xff, CF = 1
```

Permits more: REMS, by the source reading. The `_DIFF` theorems
take register 0 equal to 0xff (0xffff at 16 bits) and the count equal to
the width: REMS permits the final state with CF clear, PF and SF set and
ZF clear, and s2n-bignum rejects it because it sets CF. 32- and 64-bit
SAR cannot reach these counts after masking, and their REMS theorems are
`_EQ`.

## rems-rotate-zero-of

At masked count zero, REMS's ROL and ROR put OF in their undefined-flag
mask, so `write_user_rflags` writes an unknown OF. s2n-bignum preserves
OF.

```text
initial:  EAX = 0, OF = 0
ROL EAX,0
REMS:     EAX = 0, OF = 0 or 1
s2n:      EAX = 0, OF = 0
```

REMS follows Intel's Operation pseudocode, which defines OF only for a
masked count of one; Intel's Flags Affected paragraph says that a masked
count of zero affects no flags. The two texts disagree, so this entry
makes no classification.

Permits more: REMS, by the source reading. One conjunct of each
`SAIL_HL_X86_REMS_ROL*_RI_DIFF` and `SAIL_HL_X86_REMS_ROR*_RI_DIFF` takes
register 0 equal to 0 and count 0: REMS permits the final state with OF
set, and s2n-bignum rejects it.

## rems-rotate-wide-count

REMS's 8- and 16-bit rotates pass the masked count to the rotate helper
without reducing it modulo the rotated width: 8 or 16 bits for ROL and
ROR, 9 or 17 bits for RCL and RCR (`model/rotates_spec.sail:7,34,145,172,
288,315,426,453`). Byte and word counts are masked to 0 to 31, so the
count can exceed the width. `rotate_left_bits` and `rotate_right_bits`
(`model/prelude.sail:510-532`) then shift by `width - count`, a negative
amount.

```text
ROR AL,9
Intel:    rotate right by (9 AND 1FH) MOD 8 = 1
REMS:     (AL >> 9) | (AL << (8 - 9))
```

Sail's shift primitives give negative amounts no single meaning. In the
pinned Sail, the OCaml library's `shiftl` returns an empty bitvector and
its `shiftr` returns the input unchanged (`src/lib/sail_lib.ml:741-757`);
the C runtime shifts by the amount's magnitude (`lib/sail.c:1273-1284`),
so ROR AL,9 computes `AL << 1`; the SMT backend gives zero. None is the
architectural rotate. The exporter therefore makes the result an unknown
word ([X86.md](X86.md#rems)). 32- and 64-bit rotates mask the count below
the width and never reach this.

```text
initial:  AL = 1, CF = 0, OF = 0
ROL AL,9
REMS:     AL = u for any u; CF = bit 0 of u; OF = 0 or 1
s2n:      AL = 2, CF = 0, OF = 0 or 1     (rotate by 9 MOD 8 = 1)
```

Permits more: REMS permits final states that s2n-bignum rejects; the
theorems do not show the converse, and for ROR the carry entry above also
applies. One conjunct of each of these theorems takes register 0 equal to
1 and a count one above the rotated width (9 or 17 for ROL and ROR, 10 or
18 for RCL and RCR): REMS permits the final state that keeps register 0
equal to 1, and s2n-bignum rejects it because it rotates by one bit. This
entry rests on the exporter's unknown value for a negative shift; under
the OCaml runtime's `shiftr`, ROL and RCL would also keep the value 1.
