# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# The settings shared by the scripts here, which source this file. All
# that they download or build goes under WORK, and any of these can be
# set in the environment instead:
#
#   WORK          downloads, builds and results (default: work/ here)
#   MLKEM_NATIVE  a checkout of mlkem-native at MLKEM_NATIVE_COMMIT, the
#                 reference (default: WORK/mlkem-native, made by setup.sh)
#   VECTORS       the ACVP and Wycheproof vectors (default: WORK/vectors)
#   VALGRIND      a valgrind that can run the code under test (default:
#                 on AArch64, WORK/valgrind/bin/valgrind if setup.sh built
#                 it, since the SHA3 instructions need a patched one; on
#                 x86_64, the valgrind on the PATH); if it is empty, the
#                 steps under valgrind are skipped
#   CC            the C compiler for the tests (default: gcc)
#
# The scripts run on AArch64 (for arm/mlkem_native/asm) and on x86_64 (for
# x86/mlkem_native/asm), chosen by the machine they run on (ARCH).

T=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
REPO=$(cd "$T/../.." && pwd)
ARCH=${ARCH:-$(uname -m)}
case $ARCH in
  aarch64|arm64) ARCH=aarch64 ;;
  x86_64|amd64) ARCH=x86_64 ;;
  *) echo "env.sh: unsupported machine $ARCH" >&2; exit 1 ;;
esac
WORK=${WORK:-$T/work}
MLKEM_NATIVE_COMMIT=9b96caa137514c82a097a4251783769657826f6c
MLKEM_NATIVE=${MLKEM_NATIVE:-$WORK/mlkem-native}
VECTORS=${VECTORS:-$WORK/vectors}
if [ -z "${VALGRIND+set}" ]; then
  if [ $ARCH = aarch64 ]; then
    VALGRIND=$WORK/valgrind/bin/valgrind
    [ -x "$VALGRIND" ] || VALGRIND=
  else
    VALGRIND=$(command -v valgrind || true)
  fi
fi
CC=${CC:-gcc}

if [ $ARCH = aarch64 ]; then

# The objects of a build (see build.sh): the API, the middle layer and
# the constants in arm/mlkem_native/asm, the new leaves in arm/mlkem, and
# the existing functions they call (and mlkem_rej_uniform_VARIABLE_TIME,
# which test_leaf compares with the new sampler).

NATIVE2_OBJS="mlkem512 mlkem768 mlkem1024 mlkem_gen_matrix mlkem_getnoise
  mlkem_hash_h mlkem_hash_g mlkem_native2_constants"
LEAF_OBJS="add_reduce sub_reduce cbd2 cbd3 check_encoding compress_d4
  compress_d5 compress_d10 compress_d11 decompress_d4 decompress_d5
  decompress_d10 decompress_d11 frombytes frommsg tomsg
  rej_uniform_alt_VARIABLE_TIME ntt_alt intt_alt tobytes_alt
  basemul_k2_alt basemul_k3_alt basemul_k4_alt mulcache_compute reduce
  tomont rej_uniform_VARIABLE_TIME"
SHA3_OBJS="sha3_keccak_f1600 sha3_keccak4_f1600_alt2"

# The flags that make the kernel enforce BTI in a test program, and the
# flag for BTI landing pads in compiled C

BTI_FLAGS="-mbranch-protection=bti -Wl,-z,force-bti -Wl,-e,bti_start
  -Wl,-init,bti_init -Wl,-fini,bti_init $T/bti_start.S"
CF_CFLAGS=-mbranch-protection=bti
ABI_STUB=$T/abi_stub.S

# The directory of the code, and how to assemble a per-level file
# preprocessed with extra flags (build.sh with CTFLAGS): asm_with FILE
# FLAGS OUTPUT [WINDOWS_ABI], the last for x86_64 only (default 0)

ARCHDIR=arm
asm_with() {
  cat "$1" | gcc -E -I../include $2 -xassembler-with-cpp - | tr ';' '\n' |
    as -march=armv8.2-a+sha3 -march=armv8-a+crypto -o "$3" -
}

else

# On x86_64 the objects are those of x86/mlkem_native/asm, x86/mlkem and
# x86/sha3 (filled in as they are written): the new leaves, with the same
# names and contracts as on AArch64, mlkem-native's compress and
# decompress kernels (mlkem_compress_d4_x86 and so on, which take their
# tables from the constants block), and the existing x86 kernels
# (mlkem_frombytes and mlkem_tobytes in the custom NTT order of the x86
# backend, and mlkem_unpack into it), and among the Keccak kernels also
# sha3_keccak_f1600_alt2, which mlkem_native2 does not use, for
# test_leaf. There is no enforcement of IBT on
# hosts without CET, so instead of the BTI runs the scripts check
# statically that every global function starts with endbr64
# (check_endbr.sh); leafmid.sh also checks that no instruction uses fs
# or gs (check_noseg.sh).

NATIVE2_OBJS="mlkem512 mlkem768 mlkem1024 mlkem_gen_matrix mlkem_getnoise
  mlkem_hash_h mlkem_hash_g mlkem_native2_constants"
LEAF_OBJS="add_reduce sub_reduce cbd2 cbd3 check_encoding compress_d4_x86
  compress_d5_x86 compress_d10_x86 compress_d11_x86 decompress_d4_x86
  decompress_d5_x86 decompress_d10_x86 decompress_d11_x86 frombytes
  frommsg tomsg rej_uniform_alt_VARIABLE_TIME tobytes unpack ntt intt
  mulcache_compute basemul_k2 basemul_k3 basemul_k4 reduce tomont
  rej_uniform_VARIABLE_TIME"
SHA3_OBJS="sha3_keccak4_f1600_alt sha3_keccak_f1600_alt2"
BTI_FLAGS=""
CF_CFLAGS=-fcf-protection=full
ABI_STUB=$T/abi_stub_x86.S

# The AVX-512 version (build.sh with VARIANT=avx512): its API and middle
# layer and its Keccak-f1600 permutations in x86/mlkem_native/asm_avx512,
# used with the leaves and the constants block above

AVX512_N2_OBJS="mlkem512_avx512 mlkem768_avx512 mlkem1024_avx512
  mlkem_gen_matrix_avx512 mlkem_getnoise_avx512 mlkem_hash_h_avx512
  mlkem_hash_g_avx512"
AVX512_LEAF_OBJS="sha3_keccak_f1600_avx512 sha3_keccak4_f1600_avx512"

ARCHDIR=x86
asm_with() {
  cat "$1" | gcc -E -I../include -DWINDOWS_ABI=${4:-0} $2 \
    -xassembler-with-cpp - | tr ';' '\n' | as -o "$3" -
}

fi

result() {
  if [ "$2" = 0 ]; then echo "  $1: OK"
  elif [ "$2" = skip ]; then echo "  $1: skipped"
  else echo "  $1: FAIL"; st=1; fi
}
