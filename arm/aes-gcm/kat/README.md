# AES-256-GCM whole-blocks DECRYPT — Phase-0 KAT gate

Mechanical validation of the frozen `aesv8_gcm_8x_dec_256_wb.o` binary on
whole-block inputs **longer than 8 blocks** — the main-loop
(`.L256_dec_main_loop`, 0x4a0..0x9ec) and prepretail (0x9f0..0xec0) machine code
that the HOL Light proof has not yet executed. This gate must PASS before any
main-loop proof work begins (it catches the guard-shifted-PC / ABI-clobber /
byteswap bug class in seconds instead of mid-proof).

Host must be **aarch64** — the `.o` objects run natively.

## Running

```sh
make            # PRIMARY differential gate (self-contained, no aws-lc)
make absolute   # ABSOLUTE enc->dec round-trip (assembles read-only aws-lc asm)
make all        # both
```

Both exit non-zero on any failure.

## The two checks

### Primary — differential (`kat_wb_dec.c`)

`aesv8_gcm_8x_dec_256_wb.o` was derived from the trusted upstream sibling
`aesv8_gcm_8x_dec_256.o` by exactly two edits (confirmed by disassembly diff):
an entry guard (`tst x1,#127; b.ne`) and DELETION of the partial-last-block
masking tail. The entire main-loop + prepretail + whole-block tail is
**byte-identical**. On whole-block input the two functions must therefore
produce identical `out`, `Xi`, `ivec`, and return value.

Because neither binary has any *data-dependent* branch (AES/GHASH/CTR are
straight-line constant-time; every branch is *length*-dependent), the
differential is valid with **arbitrary but identical** key/Htable/ivec/Xi/ct
material — no cryptographically consistent H-table is needed, so this gate has
no external dependency. It also asserts non-degeneracy (output ≠ input, Xi
advanced).

### Absolute — encrypt→decrypt round-trip (`kat_wb_dec_absolute.c`)

Builds a **real** AES-256 schedule (`aes_hw_set_encrypt_key`) and a **real**
H^1..H^8 table (`H = E_K(0)` via `aes_hw_encrypt`, then `gcm_init_v8` — these
aws-lc aarch64 asm files are assembled in **read-only**, aws-lc is not
modified). Encrypts a known plaintext with the trusted `aesv8_gcm_8x_enc_256.o`,
then decrypts with the target `_wb` kernel and asserts the plaintext is
recovered **and** the decrypt's final GHASH accumulator equals the encrypt's
(tag consistency against an independently-derived kernel).

## Coverage

Both sweep `nblk` across all three control-flow legs, with trip count
`q = (nblk-9) DIV 8` full main-loop-body iterations:

| nblk    | leg                         | loop body |
|---------|-----------------------------|-----------|
| 1..8    | early `b.ge .L256_dec_tail` (DISPATCH) | no |
| 9..16   | `b.ge .L256_dec_prepretail` | no (q=0) |
| ≥17     | main-loop body, then prepretail + tail(r) | yes (q≥1) |

The `≥17` cases cover every tail remainder `r = nblk - 8*(q+1)` in `1..8` and
run up to q=30 iterations (nblk=256).

## Result (2026-07-25)

- Differential: **35/35 PASS**, 19 body cases. `KAT GATE: PASS`.
- Absolute round-trip: **23/23 PASS**, 14 body cases. `ABSOLUTE KAT: PASS`.
