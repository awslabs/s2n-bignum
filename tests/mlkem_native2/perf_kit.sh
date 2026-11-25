#!/bin/bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
#
# perf_kit.sh: compare the speed of the ML-KEM API in assembly of
# s2n-bignum (the build asm of arm/mlkem_native or x86/mlkem_native and,
# where the CPU has AVX-512, asm_avx512 of x86/mlkem_native) with the
# fastest of several builds of mlkem-native with its native backends, on
# the machine it runs on.
#
# usage: perf_kit.sh [WORKDIR]      (default ./mlkem-perf)
#
# The script stands alone: it can be fetched by itself and run anywhere,
#
#   curl -O https://raw.githubusercontent.com/awslabs/s2n-bignum/native-unify/tests/mlkem_native2/perf_kit.sh
#   bash perf_kit.sh ~/mlkem-perf
#
# It fetches (or updates) s2n-bignum (or uses the checkout S2N_DIR) and
# mlkem-native under WORKDIR and builds:
#  - s2n-bignum's assembly, with tests/mlkem_native2/build.sh (the rules
#    of its Makefiles);
#  - mlkem-native, for each combination of
#      ref       MLKEM_REFS: "pinned" (the commit that tests/mlkem_native2
#                checks the assembly against) and "main" by default;
#      compiler  COMPILERS: gcc and clang by default;
#      style     STYLES: "multilevel", one object per source file
#                (examples/multilevel_build_native), and "mono", all of it
#                in one translation unit, so the compiler sees it all
#                (examples/monolithic_build_multilevel_native);
#      flags     FLAGS: "O3", the flags of the examples (-O3, and the
#                native backends that auto.mk finds the host supports),
#                and "native", the same with -march=native added;
#      ISA       on x86_64 with AVX-512 only, where the build can use it
#                (with -march=native, or for refs whose auto.mk turns on
#                mlkem-native's AVX-512 Keccak-f1600, which it has since
#                November 2026): "avx512", and "avx2" with AVX-512 turned
#                off (-mno-avx512f, MK_COMPILER_SUPPORTS_AVX512=0).
# It then measures each library with tests/mlkem_native2/bench_api.c:
# keypair_derand (key generation), keypair, enc_derand (encapsulation),
# enc, dec (decapsulation), check_pk and check_sk, for ML-KEM-512, -768
# and -1024, each the median of 31 runs of 200 calls; on x86_64 it also
# gives the time per call, as the clock varies. All the libraries are
# measured in turn, ROUNDS times, in a different order each round.
#
# The report gives, for each function, the median over the rounds, the
# fastest mlkem-native build for that function on this machine, and the
# speedup of the assembly over it: in time on x86_64, in cycles on AArch64
# (whose clock does not vary). On x86_64 with AVX-512 the AVX2 assembly is
# compared with the mlkem-native builds without AVX-512, and the AVX-512
# assembly with all of them. "spread" is (max - min) / median over the
# rounds, for the two numbers compared: differences smaller than it are
# noise. The fastest build may differ from one function to another and
# from one machine to another, which is why every combination is built.
#
# Requirements: Linux on AArch64 with the SHA3 extension (Graviton 3 and
# 4, for example) or on x86_64 with AVX2; git, make, python3, binutils
# (as, nm, objcopy, ar), gcc and/or clang, and taskset (util-linux) to pin
# the runs to a core. An otherwise idle machine: other work skews the
# results.
#
# Environment (all optional):
#   S2N_REPO    s2n-bignum repository (https://github.com/awslabs/s2n-bignum)
#   S2N_REF     its branch, tag or commit (native-unify)
#   S2N_DIR     an s2n-bignum checkout to use instead of fetching one,
#               e.g. $(git rev-parse --show-toplevel) to measure one's own
#   MLKEM_REPO  mlkem-native repository
#               (https://github.com/pq-code-package/mlkem-native)
#   MLKEM_REFS  mlkem-native refs ("pinned main"); any branch, tag or commit
#   COMPILERS   compilers for mlkem-native (gcc and clang, those found;
#               the newest clang-NN if there is no plain clang); for
#               example "gcc-12 gcc-14 clang-17 clang-19"
#   STYLES      ("multilevel mono")
#   FLAGS       ("O3 native")
#   ROUNDS      (11; 3 for a quick look)
#   CORE        CPU to pin the runs to (default: the last one); "none"
#   OFFLINE     1: do not fetch, use what WORKDIR has
#   CC          compiler for the benchmark harness and the C parts of the
#               assembly build (gcc, else cc)
#
# Results go to WORKDIR/results/HOST-DATE/: summary.txt (also printed),
# results.csv (every library and function), machine.txt, libs.txt and the
# raw output of each run.

set -euo pipefail

W=$(mkdir -p "${1:-mlkem-perf}" && cd "${1:-mlkem-perf}" && pwd)
S2N_REPO=${S2N_REPO:-https://github.com/awslabs/s2n-bignum}
S2N_REF=${S2N_REF:-native-unify}
MLKEM_REPO=${MLKEM_REPO:-https://github.com/pq-code-package/mlkem-native}
MLKEM_REFS=${MLKEM_REFS:-pinned main}
STYLES=${STYLES:-multilevel mono}
FLAGS=${FLAGS:-O3 native}
ROUNDS=${ROUNDS:-11}
OFFLINE=${OFFLINE:-0}

say() { echo "== $*"; }
die() { echo "perf_kit.sh: $*" >&2; exit 1; }

# ------------------------------------------------------------------------
# The machine and the tools
# ------------------------------------------------------------------------

[ "$(uname -s)" = Linux ] || die "Linux only"
ARCH=$(uname -m)
case $ARCH in
  aarch64|arm64)
    ARCH=aarch64
    grep -qw sha3 /proc/cpuinfo ||
      die "the assembly needs the SHA3 extension (Graviton 3 or 4, say)" ;;
  x86_64)
    grep -qw avx2 /proc/cpuinfo || die "the assembly needs AVX2" ;;
  *) die "AArch64 or x86_64 only, not $ARCH" ;;
esac
AVX512=0
if [ $ARCH = x86_64 ] && grep -qw avx512f /proc/cpuinfo &&
   grep -qw avx512vl /proc/cpuinfo && grep -qw avx512dq /proc/cpuinfo; then
  AVX512=1
fi
for t in git make python3 as nm objcopy ar; do
  command -v $t > /dev/null || die "$t not found"
done
if [ -z "${CC:-}" ]; then
  if command -v gcc > /dev/null; then CC=gcc; else CC=cc; fi
fi
export CC
if [ -z "${COMPILERS:-}" ]; then
  COMPILERS=""
  command -v gcc > /dev/null && COMPILERS="gcc"
  if command -v clang > /dev/null; then
    COMPILERS="$COMPILERS clang"
  else
    c=$(compgen -c clang- | grep -E '^clang-[0-9]+$' | sort -t- -k2 -n |
        tail -1 || true)
    [ -n "$c" ] && COMPILERS="$COMPILERS $c"
  fi
  [ -n "$COMPILERS" ] || die "no gcc or clang for mlkem-native"
fi
NCPU=$(nproc)
PIN=""
if [ "${CORE:-}" != none ]; then
  CORE=${CORE:-$((NCPU - 1))}
  if command -v taskset > /dev/null; then
    PIN="taskset -c $CORE"
  else
    echo "(no taskset: the runs are not pinned to a core)"
  fi
fi
LOAD=$(cut -d' ' -f1 /proc/loadavg)
python3 -c "import sys; sys.exit(0 if float('$LOAD') < 1.0 else 1)" ||
  echo "(warning: load average $LOAD; other work on the machine skews" \
       "the results)"

# ------------------------------------------------------------------------
# The sources
# ------------------------------------------------------------------------

if [ -n "${S2N_DIR:-}" ]; then
  S2N=$(cd "$S2N_DIR" && pwd)
  S2N_REF="checkout $S2N"
else
  S2N=$W/s2n-bignum
fi
if [ -z "${S2N_DIR:-}" ] && [ "$OFFLINE" != 1 ]; then
  say "fetching s2n-bignum $S2N_REF"
  if [ ! -d "$S2N/.git" ]; then
    git init -q "$S2N"; git -C "$S2N" remote add origin "$S2N_REPO"
  fi
  git -C "$S2N" fetch -q --depth 1 origin "$S2N_REF"
  git -C "$S2N" -c advice.detachedHead=false checkout -q --force FETCH_HEAD
fi
[ -f "$S2N/tests/mlkem_native2/bench_api.c" ] ||
  die "$S2N has no tests/mlkem_native2 (S2N_REF=$S2N_REF)"
T=$S2N/tests/mlkem_native2
PINNED=$(sed -n 's/^MLKEM_NATIVE_COMMIT=\([0-9a-f]*\).*/\1/p' "$T/env.sh")

MN=$W/mlkem-native
if [ "$OFFLINE" != 1 ]; then
  say "fetching mlkem-native"
  [ -d "$MN/.git" ] || git clone -q "$MLKEM_REPO" "$MN"
  git -C "$MN" fetch -q --tags origin
fi
resolve() {
  case $1 in
    pinned) echo "$PINNED" ;;
    main|master) git -C "$MN" rev-parse origin/$1 ;;
    *) git -C "$MN" rev-parse --verify "$1^{commit}" ;;
  esac
}

# ------------------------------------------------------------------------
# The libraries
# ------------------------------------------------------------------------

B=$W/build; mkdir -p "$B/lib"
LIBS=""                        # the libraries, in order
: > "$B/lib/isa.txt"           # LIBRARY ISA, for the report
addlib() { LIBS="$LIBS $1"; echo "$1 $2" >> "$B/lib/isa.txt"; }

# s2n-bignum's assembly. The objects are linked as they are, not from an
# archive, so that the randomized keypair and enc of randomized.c, which
# bench_api.c only references weakly, are linked too.
export WORK=$B/s2n
S2N_SHA=$(git -C "$S2N" rev-parse HEAD 2> /dev/null ||
          echo "not a git checkout")
S2N_SHORT=$S2N_SHA
[ ${#S2N_SHA} = 40 ] && S2N_SHORT=${S2N_SHA:0:12}
say "s2n-bignum assembly ($S2N_SHORT)"
bash "$T/build.sh" > "$B/s2n-build.log" 2>&1 ||
  { tail -20 "$B/s2n-build.log"; die "s2n-bignum build failed"; }
ls "$WORK"/obj/*.o > "$B/lib/asm.inputs"
if [ $ARCH = x86_64 ]; then addlib asm avx2; else addlib asm aarch64; fi
if [ $AVX512 = 1 ]; then
  VARIANT=avx512 bash "$T/build.sh" > "$B/s2n-build-avx512.log" 2>&1 ||
    { tail -20 "$B/s2n-build-avx512.log"; die "AVX-512 build failed"; }
  ls "$WORK"/obj_avx512/*.o > "$B/lib/asm_avx512.inputs"
  addlib asm_avx512 avx512
fi

# The CFLAGS of an mlkem-native example, as its Makefile computes them
# (with the native backends that its auto.mk finds), for compiler $2 and
# the extra make variables $3...
printf 'print-cflags:\n\t@echo $(CFLAGS)\n' > "$B/print-cflags.mk"
cflags_of() {
  local ex=$1 cc=$2; shift 2
  CC=$cc make -s -C "$ex" -f Makefile -f "$B/print-cflags.mk" "$@" \
    print-cflags
}

# Build mlkem-native from source tree $1 as library $2 with compiler $3,
# style $4, extra CFLAGS $5 and extra make variables $6
build_mlkem() {
  local src=$1 name=$2 cc=$3 style=$4 xcf=$5 mv=$6
  local out=$B/$name
  rm -rf "$out"; mkdir -p "$out/objs"
  case $style in
    multilevel)
      local ex=$src/examples/multilevel_build_native
      CC=$cc CFLAGS="$xcf" make -s -C "$ex" BUILD_DIR="$out/objs" $mv \
        mlkem_objs -j"$NCPU" > "$out/build.log" 2>&1 || return 1
      rm -f "$B/lib/$name.a"
      ar rcs "$B/lib/$name.a" $(find "$out/objs" -name '*.o' | sort) ;;
    mono)
      # The example includes mlkem_native_all.c in its main program, with
      # the API static; built here as a library with the API external
      local ex=$src/examples/monolithic_build_multilevel_native f
      f=$(CFLAGS="$xcf" cflags_of "$ex" "$cc" $mv 2> "$out/build.log") ||
        return 1
      sed 's/^#define MLK_CONFIG_EXTERNAL_API_QUALIFIER static$//' \
        "$ex/mlkem_native/mlkem_native_config.h" > "$out/config.h"
      (cd "$ex" &&
       $cc $f "-DMLK_CONFIG_FILE=\"$out/config.h\"" -Imlkem_native -I. \
         -c mlkem_native_all.c -o "$out/objs/all.o" &&
       $cc $f "-DMLK_CONFIG_FILE=\"$out/config.h\"" \
         -DMLK_CONFIG_MULTILEVEL_WITH_SHARED -Imlkem_native -I. \
         -c mlkem_native/mlkem_native_asm.S -o "$out/objs/asm.o") \
        >> "$out/build.log" 2>&1 || return 1
      rm -f "$B/lib/$name.a"
      ar rcs "$B/lib/$name.a" "$out/objs/all.o" "$out/objs/asm.o" ;;
    *) die "unknown style $style" ;;
  esac
  echo "$B/lib/$name.a" > "$B/lib/$name.inputs"
}

for ref in $MLKEM_REFS; do
  sha=$(resolve "$ref") || die "no mlkem-native ref $ref"
  short=$(git -C "$MN" rev-parse --short=8 "$sha")
  src=$B/mlkem-native-$short
  [ -d "$src" ] || git -C "$MN" worktree add -q --detach "$src" "$sha"
  # Whether this ref's auto.mk can turn AVX-512 on (and off)
  knows512=0
  grep -q MK_COMPILER_SUPPORTS_AVX512 \
    "$src/examples/multilevel_build_native/auto.mk" 2> /dev/null &&
    knows512=1
  for cc in $COMPILERS; do
    for style in $STYLES; do
      for fl in $FLAGS; do
        # The ISA variants (VARIANT|TAG|EXTRA_CFLAGS|MAKE_VARIABLES). On
        # x86_64 with AVX-512 there are two where the build can use
        # AVX-512: "avx512", and "avx2" with AVX-512 turned off, both in
        # auto.mk and, with -march=native, in the compiler
        # (-mno-avx512f), so that the AVX2 assembly is compared with
        # code that does not use AVX-512 either.
        case $fl in
          O3) xcf="" ;;
          native) xcf="-march=native" ;;
          *) die "unknown FLAGS entry $fl (O3 or native)" ;;
        esac
        if [ $ARCH = aarch64 ]; then
          variants=("-|aarch64|$xcf|")
        elif [ $AVX512 = 0 ]; then
          variants=("-|avx2|$xcf|")
        elif [ $fl = native ] || [ $knows512 = 1 ]; then
          m=""; [ $knows512 = 1 ] && m="MK_COMPILER_SUPPORTS_AVX512=0"
          nx="$xcf"; [ $fl = native ] && nx="$xcf -mno-avx512f"
          variants=("avx512|avx512|$xcf|" "avx2|avx2|$nx|$m")
        else
          variants=("-|avx2|$xcf|")
        fi
        for v in "${variants[@]}"; do
          IFS='|' read -r vn tag vx mv <<< "$v"
          name=mlkem-native-$ref-$cc-$style-$fl
          [ "$vn" = - ] || name=$name-$vn
          say "$name ($short)"
          if build_mlkem "$src" "$name" "$cc" "$style" "$vx" "$mv"; then
            addlib "$name" "$tag"
          else
            echo "   (build failed, skipped: $B/$name/build.log)"
          fi
        done
      done
    done
  done
done

# The benchmark programs
for lib in $LIBS; do
  if ! $CC -O2 -o "$B/bench_$lib" "$T/bench_api.c" \
         $(cat "$B/lib/$lib.inputs") > "$B/link_$lib.log" 2>&1; then
    echo "   (cannot link the benchmark with $lib, skipped:" \
         "$B/link_$lib.log)"
    LIBS=$(echo " $LIBS " | sed "s/ $lib / /")
  fi
done

# ------------------------------------------------------------------------
# The measurements
# ------------------------------------------------------------------------

R=$W/results/$(hostname -s)-$(date -u +%Y%m%dT%H%M%SZ)
mkdir -p "$R/raw"
cp "$B/lib/isa.txt" "$R/libs.txt"
{
  echo "host: $(hostname)"
  echo "date: $(date -u)"
  echo "kernel: $(uname -sr)"
  echo "cpu: $(grep -m1 -E '^(model name|Model name)' /proc/cpuinfo |
               cut -d: -f2- | sed 's/^ *//')"
  if command -v lscpu > /dev/null; then
    lscpu | grep -E '^(Model name|Vendor ID|CPU\(s\)|Thread|Core|Socket)' ||
      true
  fi
  echo "arch: $ARCH; AVX-512: $([ $AVX512 = 1 ] && echo yes || echo no)"
  echo "pinned to core: ${CORE:-none}"
  echo "load at start: $(cat /proc/loadavg)"
  echo "s2n-bignum $S2N_REF: $S2N_SHA"
  for ref in $MLKEM_REFS; do
    echo "mlkem-native $ref: $(resolve "$ref")"
  done
  for cc in $(echo "$CC $COMPILERS" | tr ' ' '\n' | awk '!seen[$0]++'); do
    echo "$cc: $($cc --version | head -1)"
  done
} > "$R/machine.txt"

set -- $LIBS
NL=$#
say "measuring $NL libraries, $ROUNDS rounds (about $((NL * 4)) s each)"
for r in $(seq 1 "$ROUNDS"); do
  k=$(( (r - 1) % NL ))
  for lib in "${@:k+1}" "${@:1:k}"; do
    $PIN "$B/bench_$lib" "$lib" > "$R/raw/$lib.$r.txt"
  done
  printf '   round %d of %d\n' "$r" "$ROUNDS"
done
echo "load at end: $(cat /proc/loadavg)" >> "$R/machine.txt"

python3 -I - "$R" "$ARCH" $LIBS <<'PY' | tee "$R/summary.txt"
import os, sys, statistics
R, arch, libs = sys.argv[1], sys.argv[2], sys.argv[3:]
isa = dict(l.split() for l in open(os.path.join(R, 'libs.txt')))
raw = os.path.join(R, 'raw')
data = {}            # data[lib][func] = [(cycles, ns or None), ...]
for f in sorted(os.listdir(raw)):
    lib = f.rsplit('.', 2)[0]
    for line in open(os.path.join(raw, f)):
        if line.startswith('#') or not line.strip(): continue
        p = line.split()
        ns = float(p[2]) if len(p) > 3 and p[3] == 'ns' else None
        data.setdefault(lib, {}).setdefault(p[0], []).append(
            (float(p[1]), ns))
timed = arch == 'x86_64'
key = 1 if timed else 0
unit = 'ns' if timed else 'cycles'
def vals(l, fn):
    return [x[key] for x in data.get(l, {}).get(fn, []) if x[key] is not None]
def med(l, fn):
    v = vals(l, fn); return statistics.median(v) if v else None
def spread(l, fn):
    v = vals(l, fn)
    return (max(v) - min(v)) / statistics.median(v) if len(v) > 1 else 0.0
ours = [l for l in libs if l.startswith('asm')]
natives = [l for l in libs if not l.startswith('asm')]
funcs = []
for l in libs:
    for fn in data.get(l, {}):
        if fn not in funcs: funcs.append(fn)
with open(os.path.join(R, 'results.csv'), 'w') as out:
    out.write('library,isa,function,median_%s,spread,rounds\n' % unit)
    for l in libs:
        for fn in funcs:
            if med(l, fn) is not None:
                out.write('%s,%s,%s,%.0f,%.3f,%d\n' % (
                    l, isa[l], fn, med(l, fn), spread(l, fn),
                    len(vals(l, fn))))
print(open(os.path.join(R, 'machine.txt')).read().rstrip())
print()
print('Medians over the rounds, in %s. speedup = fastest mlkem-native '
      'build / assembly;' % unit)
print('spread = (max - min) / median over the rounds, the larger of the '
      'two; "build" is')
print('the fastest mlkem-native build: ref-compiler-style-flags[-isa].')
for o in ours:
    if isa[o] == 'avx512':
        cands = natives
        what = 'all the mlkem-native builds'
    else:
        cands = [l for l in natives if isa[l] == isa[o]]
        what = ('the mlkem-native builds without AVX-512'
                if isa[o] == 'avx2' else 'all the mlkem-native builds')
    if not cands: continue
    print()
    print('%s against %s:' % (o, what))
    print('%-26s %12s %10s %8s %7s  %s' % ('function', 'mlkem-native',
                                         o, 'speedup', 'spread', 'build'))
    for fn in funcs:
        c = [(med(l, fn), l) for l in cands if med(l, fn)]
        v = med(o, fn)
        if not c or not v: continue
        best, bl = min(c)
        sp = max(spread(bl, fn), spread(o, fn))
        print('%-26s %12.0f %10.0f %7.2fx %6.1f%%  %s' % (
            fn, best, v, best / v, 100 * sp,
            bl.replace('mlkem-native-', '')))
main = [fn for fn in funcs if fn.split('_', 1)[1] in
        ('keypair_derand', 'enc_derand', 'dec')]
short = {'keypair_derand': 'keygen', 'enc_derand': 'enc', 'dec': 'dec'}
print()
print('Every build, median %s:' % unit)
print('%-44s' % 'library' + ''.join(
    ' %8s' % (fn.split('_', 1)[0][5:] + short[fn.split('_', 1)[1]][:3])
    for fn in main))
for l in libs:
    print('%-44s' % l + ''.join(
        ' %8s' % ('%.0f' % med(l, fn) if med(l, fn) else '-') for fn in main))
print()
print('Results in', R)
PY
