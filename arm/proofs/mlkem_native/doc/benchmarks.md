# Benchmarks of the gcc12_O2 and gcc12_O2_mono proofs

Every proof of both builds was run once at 19f9abc7 (with the GOT tactic
fix of 2f3ed758 applied), one proof per CPU on 16 dedicated CPUs (32-47)
of a 64-CPU AArch64 machine (Arm Neoverse V1, 494 GB), with other work
kept off those CPUs. Each run is the `.native` binary that `make` builds
(`tools/build-proof.sh`), so its time is what `make <f>.correct` takes
after compiling.

- **full**: the "Running time" the proof prints: wall time of the whole
  run, which re-proves every file in the file's `needs` closure.
- **own**: the file's own share: full minus the own times of all other
  proof files in its closure (each file is proved once per run, so the
  full time is the sum of the own times of its closure). Shared tactic
  files are charged to the first proof that loads them; the base
  (`arm/proofs/base.ml`, the image definition) to `libmlkem`.
- **CPU**: user CPU time of the full run. **mem**: peak resident memory.

The runs took place on 2026-11-06 between 12:02 and 18:09 UTC. Other
work ran on CPUs 0-31 at the same time (proof runs and compilation, and
at times an unrelated project on CPUs 0-47); the 1-minute load average
when a run started was 9.6 to 42 (median 25). The runs therefore share
memory bandwidth and caches with other work. A measure of the noise: own
times are differences of large full times, and for 12 of the 182 proof
files they come out slightly negative (down to -234 s for a 5737-s run),
shown as ≈0 below.

## Summary

| | gcc12_O2 | gcc12_O2_mono |
|---|---|---|
| proof files | 117 | 65 |
| sum of full runs | 51.3 h | 29.6 h |
| sum of own times (each file once) | 5.5 h | 4.7 h |
| longest full run | 130 min | 98 min |
| median own time | 43 s | 96 s |
| peak memory, largest | 918 MB | 918 MB |
| shared files, own times (loaded by every run) | 0.1 h | |

The sum of full runs is what `make` of every proof costs today; the sum
of own times is what it would cost if each file were proved once (see
[automation.md](automation.md), section 2).

## Same-named files, own time

The 15 same-named files with the largest own time in mono:

| file | O2 own | mono own | ratio |
|---|---|---|---|
| `indcpa_enc_k4` | 25 min | 37 min | 1.5 |
| `indcpa_keypair_derand_k4` | 17 min | 29 min | 1.7 |
| `indcpa_enc_k2` | 19 min | 26 min | 1.4 |
| `indcpa_enc_k3` | 21 min | 24 min | 1.1 |
| `indcpa_keypair_derand_k3` | 15 min | 18 min | 1.2 |
| `indcpa_keypair_derand_k2` | 14 min | 18 min | 1.3 |
| `gen_matrix_k4` | 14 min | 14 min | 1.0 |
| `dec_k4` | 14 min | 11 min | 0.8 |
| `dec_k3` | 453 s | 11 min | 1.4 |
| `gen_matrix_k3` | 369 s | 484 s | 1.3 |
| `dec_k2` | 334 s | 460 s | 1.4 |
| `poly_rej_uniform_x4` | 301 s | 376 s | 1.2 |
| `poly_getnoise_eta1_4x_k4` | 257 s | 237 s | 0.9 |
| `enc_k4` | 36 s | 231 s | 6.4 |
| `shake256x4` | 227 s | 229 s | 1.0 |

## Shared files

Files that proofs load but that are not proofs of functions, timed alone
(`needs` of just that file); own time as above. The ten largest:

| file | own | full (with its closure) |
|---|---|---|
| `common/mlkem_mldsa.ml` | 117 s | 186 s |
| `Library/ringtheory.ml` | 68 s | 68 s |
| `arm/proofs/base.ml` | 49 s | 69 s |
| `Library/bitmatch.ml` | 7 s | 7 s |
| `Library/words.ml` | 7 s | 7 s |
| `arm/proofs/utils/mlkem_native_fips203.ml` | 7 s | 267 s |
| `Library/pocklington.ml` | 4 s | 4 s |
| `arm/proofs/mlkem_native/polyvec_inline.ml` | 3 s | 72 s |
| `arm/proofs/utils/mlkem_native_image.ml` | 3 s | 72 s |
| `common/fips203.ml` | 3 s | 78 s |

## All gcc12_O2 proofs

| file | full | own | CPU | mem | files loaded (proofs and shared) |
|---|---|---|---|---|---|
| `basemul_k2` | 226 s | 35 s | 239 s | 790 MB | 25 |
| `basemul_k3` | 245 s | 54 s | 259 s | 790 MB | 25 |
| `basemul_k4` | 258 s | 67 s | 272 s | 791 MB | 25 |
| `check_pk_k2` | 524 s | 178 s | 536 s | 905 MB | 32 |
| `check_pk_k3` | 559 s | 178 s | 572 s | 790 MB | 32 |
| `check_pk_k4` | 10 min | 180 s | 10 min | 905 MB | 32 |
| `check_sk_k2` | 19 min | 43 s | 19 min | 774 MB | 33 |
| `check_sk_k3` | 19 min | 32 s | 19 min | 796 MB | 33 |
| `check_sk_k4` | 19 min | 50 s | 19 min | 782 MB | 33 |
| `dec_k2` | 100 min | 334 s | 100 min | 872 MB | 89 |
| `dec_k3` | 110 min | 453 s | 110 min | 856 MB | 87 |
| `dec_k4` | 130 min | 14 min | 130 min | 788 MB | 88 |
| `enc_derand_k2` | 97 min | 308 s | 98 min | 804 MB | 85 |
| `enc_derand_k3` | 101 min | 129 s | 101 min | 884 MB | 82 |
| `enc_derand_k4` | 121 min | 400 s | 121 min | 805 MB | 84 |
| `enc_k2` | 98 min | 47 s | 98 min | 913 MB | 86 |
| `enc_k3` | 107 min | 367 s | 107 min | 783 MB | 83 |
| `enc_k4` | 121 min | 36 s | 121 min | 786 MB | 85 |
| `gen_matrix_k2` | 44 min | 173 s | 44 min | 858 MB | 49 |
| `gen_matrix_k3` | 47 min | 369 s | 47 min | 859 MB | 49 |
| `gen_matrix_k4` | 55 min | 14 min | 55 min | 794 MB | 49 |
| `indcpa_dec_k2` | 20 min | 296 s | 20 min | 914 MB | 46 |
| `indcpa_dec_k3` | 21 min | 291 s | 21 min | 800 MB | 46 |
| `indcpa_dec_k4` | 22 min | 307 s | 23 min | 914 MB | 46 |
| `indcpa_enc_k2` | 86 min | 19 min | 86 min | 804 MB | 78 |
| `indcpa_enc_k3` | 92 min | 21 min | 92 min | 918 MB | 75 |
| `indcpa_enc_k4` | 107 min | 25 min | 107 min | 918 MB | 77 |
| `indcpa_keypair_derand_k2` | 77 min | 14 min | 77 min | 870 MB | 72 |
| `indcpa_keypair_derand_k3` | 82 min | 15 min | 82 min | 916 MB | 72 |
| `indcpa_keypair_derand_k4` | 93 min | 17 min | 93 min | 916 MB | 72 |
| `keccak_absorb_once` | 16 min | 270 s | 16 min | 905 MB | 30 |
| `keccak_absorb_once_x4` | 27 min | 520 s | 27 min | 784 MB | 33 |
| `keccakf1600_extract_bytes` | 199 s | 8 s | 212 s | 760 MB | 25 |
| `keccakf1600_permute` | 12 min | 504 s | 12 min | 781 MB | 27 |
| `keccakf1600_xor_bytes` | 198 s | 7 s | 211 s | 761 MB | 25 |
| `keccakf1600x4_extract_bytes` | 271 s | 72 s | 285 s | 759 MB | 26 |
| `keccakf1600x4_permute` | 12 min | 54 s | 13 min | 808 MB | 28 |
| `keccakf1600x4_xor_bytes` | 270 s | 72 s | 283 s | 777 MB | 26 |
| `keypair_derand_k2` | 77 min | ≈0 | 77 min | 821 MB | 75 |
| `keypair_derand_k3` | 83 min | 10 s | 84 min | 801 MB | 75 |
| `keypair_derand_k4` | 100 min | 280 s | 100 min | 834 MB | 75 |
| `keypair_k2` | 86 min | 585 s | 86 min | 796 MB | 76 |
| `keypair_k3` | 94 min | 10 min | 94 min | 790 MB | 76 |
| `keypair_k4` | 96 min | ≈0 | 96 min | 855 MB | 76 |
| `libmlkem` | 72 s | 0 s | 85 s | 135 MB | 12 |
| `poly_add` | 192 s | 1 s | 205 s | 759 MB | 25 |
| `poly_cbd2` | 193 s | 2 s | 207 s | 790 MB | 25 |
| `poly_cbd3` | 191 s | 0 s | 204 s | 849 MB | 25 |
| `poly_compress_d10` | 199 s | 8 s | 213 s | 759 MB | 25 |
| `poly_compress_d11` | 205 s | 14 s | 218 s | 761 MB | 25 |
| `poly_compress_d4` | 208 s | 17 s | 221 s | 790 MB | 25 |
| `poly_compress_d5` | 206 s | 15 s | 220 s | 790 MB | 25 |
| `poly_decompress_d10` | 192 s | 1 s | 205 s | 855 MB | 25 |
| `poly_decompress_d11` | 196 s | 5 s | 209 s | 759 MB | 25 |
| `poly_decompress_d4` | 193 s | 2 s | 207 s | 759 MB | 25 |
| `poly_decompress_d5` | 196 s | 5 s | 210 s | 853 MB | 25 |
| `poly_frombytes` | 197 s | 6 s | 210 s | 759 MB | 25 |
| `poly_frommsg` | 203 s | 12 s | 217 s | 790 MB | 25 |
| `poly_getnoise_eta1122_4x_k2` | 35 min | 196 s | 36 min | 908 MB | 40 |
| `poly_getnoise_eta1_4x_k2` | 37 min | 295 s | 37 min | 908 MB | 39 |
| `poly_getnoise_eta1_4x_k3` | 37 min | 261 s | 37 min | 910 MB | 39 |
| `poly_getnoise_eta1_4x_k4` | 36 min | 257 s | 37 min | 906 MB | 39 |
| `poly_getnoise_eta2_k2` | 18 min | 14 s | 18 min | 876 MB | 34 |
| `poly_getnoise_eta2_k4` | 18 min | ≈0 | 18 min | 889 MB | 34 |
| `poly_invntt_tomont` | 426 s | 235 s | 440 s | 791 MB | 26 |
| `poly_mulcache_compute` | 203 s | 12 s | 217 s | 760 MB | 25 |
| `poly_ntt` | 417 s | 226 s | 431 s | 760 MB | 26 |
| `poly_reduce` | 200 s | 9 s | 213 s | 904 MB | 25 |
| `poly_rej_uniform` | 21 min | 117 s | 21 min | 858 MB | 38 |
| `poly_rej_uniform_x4` | 41 min | 301 s | 41 min | 805 MB | 48 |
| `poly_sub` | 191 s | 0 s | 205 s | 850 MB | 25 |
| `poly_tobytes` | 229 s | 38 s | 243 s | 905 MB | 25 |
| `poly_tomont` | 197 s | 6 s | 211 s | 905 MB | 25 |
| `poly_tomsg` | 200 s | 9 s | 214 s | 790 MB | 25 |
| `polyvec_add_k2` | 211 s | 19 s | 225 s | 904 MB | 26 |
| `polyvec_add_k3` | 218 s | 26 s | 232 s | 864 MB | 26 |
| `polyvec_add_k4` | 234 s | 42 s | 248 s | 905 MB | 26 |
| `polyvec_compress_du_k2` | 232 s | 33 s | 245 s | 759 MB | 26 |
| `polyvec_compress_du_k3` | 236 s | 37 s | 250 s | 760 MB | 26 |
| `polyvec_compress_du_k4` | 255 s | 50 s | 269 s | 759 MB | 26 |
| `polyvec_decompress_du_k2` | 217 s | 25 s | 231 s | 785 MB | 26 |
| `polyvec_decompress_du_k3` | 226 s | 34 s | 240 s | 759 MB | 26 |
| `polyvec_decompress_du_k4` | 242 s | 46 s | 256 s | 905 MB | 26 |
| `polyvec_frombytes_k2` | 231 s | 34 s | 245 s | 759 MB | 26 |
| `polyvec_frombytes_k3` | 246 s | 49 s | 259 s | 759 MB | 26 |
| `polyvec_frombytes_k4` | 264 s | 67 s | 278 s | 759 MB | 26 |
| `polyvec_invntt_tomont_k2` | 459 s | 33 s | 473 s | 760 MB | 27 |
| `polyvec_invntt_tomont_k3` | 464 s | 38 s | 478 s | 905 MB | 27 |
| `polyvec_invntt_tomont_k4` | 468 s | 42 s | 481 s | 760 MB | 27 |
| `polyvec_mulcache_compute_k2` | 226 s | 23 s | 240 s | 760 MB | 26 |
| `polyvec_mulcache_compute_k3` | 241 s | 38 s | 254 s | 904 MB | 26 |
| `polyvec_mulcache_compute_k4` | 249 s | 46 s | 263 s | 760 MB | 26 |
| `polyvec_ntt_k2` | 437 s | 20 s | 450 s | 904 MB | 27 |
| `polyvec_ntt_k3` | 447 s | 30 s | 461 s | 904 MB | 27 |
| `polyvec_ntt_k4` | 455 s | 38 s | 468 s | 904 MB | 27 |
| `polyvec_reduce_k2` | 234 s | 34 s | 247 s | 790 MB | 26 |
| `polyvec_reduce_k3` | 242 s | 42 s | 255 s | 790 MB | 26 |
| `polyvec_reduce_k4` | 258 s | 58 s | 272 s | 758 MB | 26 |
| `polyvec_tobytes_k2` | 261 s | 32 s | 275 s | 904 MB | 26 |
| `polyvec_tobytes_k3` | 273 s | 44 s | 287 s | 904 MB | 26 |
| `polyvec_tobytes_k4` | 291 s | 62 s | 305 s | 904 MB | 26 |
| `polyvec_tomont_k2` | 218 s | 21 s | 232 s | 860 MB | 26 |
| `polyvec_tomont_k3` | 223 s | 26 s | 237 s | 859 MB | 26 |
| `polyvec_tomont_k4` | 233 s | 36 s | 247 s | 904 MB | 26 |
| `rej_uniform` | 289 s | 98 s | 303 s | 760 MB | 24 |
| `sha3_256` | 18 min | 98 s | 18 min | 834 MB | 32 |
| `sha3_512` | 17 min | 60 s | 18 min | 918 MB | 32 |
| `shake128_absorb_once` | 16 min | 8 s | 17 min | 808 MB | 31 |
| `shake128_init` | 74 s | 1 s | 88 s | 140 MB | 22 |
| `shake128_release` | 77 s | 4 s | 92 s | 150 MB | 22 |
| `shake128_squeezeblocks` | 13 min | 63 s | 13 min | 808 MB | 30 |
| `shake128x4_absorb_once` | 28 min | 42 s | 28 min | 754 MB | 36 |
| `shake128x4_init` | 73 s | 0 s | 87 s | 140 MB | 22 |
| `shake128x4_release` | 89 s | 14 s | 103 s | 156 MB | 23 |
| `shake128x4_squeezeblocks` | 16 min | 118 s | 16 min | 808 MB | 32 |
| `shake256` | 18 min | 98 s | 18 min | 791 MB | 32 |
| `shake256x4` | 32 min | 227 s | 32 min | 848 MB | 37 |

## All gcc12_O2_mono proofs

| file | full | own | CPU | mem | files loaded (proofs and shared) |
|---|---|---|---|---|---|
| `basemul_k2` | 227 s | 36 s | 241 s | 904 MB | 25 |
| `basemul_k3` | 239 s | 48 s | 252 s | 790 MB | 25 |
| `basemul_k4` | 261 s | 70 s | 274 s | 851 MB | 25 |
| `check_pk_k2` | 378 s | 177 s | 390 s | 791 MB | 30 |
| `check_pk_k3` | 391 s | 190 s | 404 s | 783 MB | 30 |
| `check_pk_k4` | 410 s | 209 s | 423 s | 856 MB | 30 |
| `check_sk_k2` | 524 s | 88 s | 538 s | 781 MB | 37 |
| `check_sk_k3` | 522 s | 86 s | 534 s | 781 MB | 37 |
| `check_sk_k4` | 520 s | 84 s | 532 s | 884 MB | 37 |
| `dec_k2` | 68 min | 460 s | 68 min | 804 MB | 69 |
| `dec_k3` | 78 min | 11 min | 78 min | 804 MB | 68 |
| `dec_k4` | 98 min | 11 min | 98 min | 804 MB | 64 |
| `enc_derand_k2` | 65 min | 128 s | 65 min | 819 MB | 67 |
| `enc_derand_k3` | 72 min | 214 s | 73 min | 775 MB | 65 |
| `enc_derand_k4` | 93 min | 218 s | 93 min | 817 MB | 64 |
| `enc_k2` | 66 min | 96 s | 67 min | 874 MB | 68 |
| `enc_k3` | 75 min | 153 s | 75 min | 796 MB | 66 |
| `enc_k4` | 97 min | 231 s | 97 min | 789 MB | 65 |
| `gen_matrix_k2` | 19 min | 152 s | 19 min | 908 MB | 39 |
| `gen_matrix_k3` | 25 min | 484 s | 25 min | 908 MB | 39 |
| `gen_matrix_k4` | 30 min | 14 min | 31 min | 908 MB | 39 |
| `indcpa_enc_k2` | 58 min | 26 min | 58 min | 918 MB | 61 |
| `indcpa_enc_k3` | 64 min | 24 min | 64 min | 918 MB | 59 |
| `indcpa_enc_k4` | 84 min | 37 min | 84 min | 918 MB | 58 |
| `indcpa_keypair_derand_k2` | 46 min | 18 min | 47 min | 767 MB | 56 |
| `indcpa_keypair_derand_k3` | 57 min | 18 min | 57 min | 881 MB | 58 |
| `indcpa_keypair_derand_k4` | 74 min | 29 min | 74 min | 782 MB | 57 |
| `keccak_absorb_once` | 320 s | 30 s | 333 s | 791 MB | 30 |
| `keccak_absorb_once_x4` | 365 s | 33 s | 378 s | 905 MB | 32 |
| `keccak_squeezeblocks_x4` | 358 s | 68 s | 371 s | 905 MB | 30 |
| `keccakf1600_permute` | 291 s | 99 s | 304 s | 804 MB | 27 |
| `keccakf1600_xor_bytes` | 71 s | ≈0 | 85 s | 146 MB | 22 |
| `keccakf1600x4_xor_bytes` | 83 s | 12 s | 96 s | 151 MB | 23 |
| `keypair_derand_k2` | 48 min | 108 s | 48 min | 899 MB | 57 |
| `keypair_derand_k3` | 59 min | 122 s | 59 min | 780 MB | 59 |
| `keypair_derand_k4` | 74 min | 17 s | 74 min | 801 MB | 58 |
| `keypair_k2` | 50 min | 121 s | 50 min | 786 MB | 58 |
| `keypair_k3` | 61 min | 153 s | 61 min | 804 MB | 60 |
| `keypair_k4` | 77 min | 152 s | 77 min | 786 MB | 59 |
| `libmlkem` | 72 s | 0 s | 86 s | 138 MB | 12 |
| `poly_cbd2` | 186 s | ≈0 | 200 s | 790 MB | 25 |
| `poly_cbd3` | 186 s | ≈0 | 198 s | 790 MB | 25 |
| `poly_compress_d10` | 190 s | ≈0 | 204 s | 791 MB | 25 |
| `poly_compress_d4` | 198 s | 7 s | 212 s | 760 MB | 25 |
| `poly_decompress_d10` | 184 s | ≈0 | 198 s | 759 MB | 25 |
| `poly_decompress_d4` | 186 s | ≈0 | 199 s | 759 MB | 25 |
| `poly_frombytes` | 184 s | ≈0 | 197 s | 854 MB | 25 |
| `poly_frommsg` | 195 s | 4 s | 207 s | 791 MB | 25 |
| `poly_getnoise_eta1_4x_k3` | 15 min | 1 s | 15 min | 772 MB | 38 |
| `poly_getnoise_eta1_4x_k4` | 15 min | 237 s | 15 min | 789 MB | 37 |
| `poly_getnoise_eta2_k2` | 435 s | 2 s | 448 s | 785 MB | 35 |
| `poly_getnoise_eta2_k4` | 433 s | 52 s | 447 s | 905 MB | 34 |
| `poly_invntt_tomont` | 355 s | 164 s | 368 s | 866 MB | 26 |
| `poly_mulcache_compute` | 193 s | 2 s | 207 s | 790 MB | 25 |
| `poly_ntt` | 341 s | 150 s | 355 s | 905 MB | 26 |
| `poly_reduce` | 184 s | ≈0 | 198 s | 790 MB | 25 |
| `poly_rej_uniform` | 505 s | 89 s | 517 s | 792 MB | 34 |
| `poly_rej_uniform_x4` | 17 min | 376 s | 17 min | 791 MB | 38 |
| `poly_tobytes` | 210 s | 19 s | 223 s | 791 MB | 25 |
| `poly_tomsg` | 190 s | ≈0 | 203 s | 790 MB | 25 |
| `rej_uniform` | 288 s | 97 s | 301 s | 791 MB | 24 |
| `sha3_256` | 436 s | 36 s | 449 s | 781 MB | 36 |
| `sha3_512` | 475 s | 39 s | 488 s | 913 MB | 37 |
| `shake256` | 386 s | 64 s | 400 s | 868 MB | 32 |
| `shake256x4` | 11 min | 229 s | 11 min | 788 MB | 35 |

