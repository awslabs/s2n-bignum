#!/bin/sh
# Reproducible build of the snappy shared library whose AArch64 machine code
# is the subject of the proofs in ../proofs/snappy.
#
#   arm/snappy/build.sh <snappy-checkout> <out-dir>
#
# The checkout must be at SNAPPY_COMMIT. The compiler is the official gcc
# 12.4.0 image, pinned by digest, run on an AArch64 host.
set -eu
SNAPPY_COMMIT=9c28114a38866f6deeaa826db918293bc28ae410
IMAGE=gcc@sha256:fa4be2f0a762fb14cc745289227d29aa32f0b55057c301d0d61a5eba46c85d99
here=$(cd "$(dirname "$0")" && pwd)
src=$(cd "$1" && pwd)
mkdir -p "$2"; out=$(cd "$2" && pwd)
test "$(git -C "$src" rev-parse HEAD)" = "$SNAPPY_COMMIT" || {
  echo "snappy checkout is not at $SNAPPY_COMMIT" >&2; exit 1; }
test -z "$(git -C "$src" status --porcelain)" || {
  echo "snappy checkout has local changes" >&2; exit 1; }

# snappy-stubs-public.h as CMake generates it (version 1.3.1 is what
# CMakeLists.txt of this commit declares; HAVE_SYS_UIO_H_01 = 1).
CXXFLAGS="-std=c++11 -O2 -fPIC -fno-exceptions -fno-rtti \
 -mbranch-protection=none -fno-stack-protector \
 -g -gdwarf-4 -DNDEBUG -DHAVE_CONFIG_H -Wall -Wextra -Wno-sign-compare"
LDFLAGS="-shared -Wl,-Bsymbolic -Wl,-z,now -Wl,-z,relro -Wl,-soname,libsnappy.so -Wl,--build-id=none"

docker run --rm --network none -u "$(id -u):$(id -g)" \
  -v "$src:/src:ro" -v "$here:/cfg:ro" -v "$out:/out" -w /out "$IMAGE" sh -euc "
  sed -e 's/\${HAVE_SYS_UIO_H_01}/1/' \
      -e 's/\${PROJECT_VERSION_MAJOR}/1/' -e 's/\${PROJECT_VERSION_MINOR}/3/' \
      -e 's/\${PROJECT_VERSION_PATCH}/1/' /src/snappy-stubs-public.h.in \
      > snappy-stubs-public.h
  cp /cfg/config.h config.h
  for f in snappy snappy-sinksource snappy-stubs-internal snappy-c; do
    g++ $CXXFLAGS -frandom-seed=\$f -ffile-prefix-map=/src=. -I/out -I/src -c /src/\$f.cc -o \$f.o
  done
  g++ $LDFLAGS -o libsnappy.so snappy.o snappy-sinksource.o \
      snappy-stubs-internal.o snappy-c.o
  g++ --version | head -1 > compiler.txt
  ld --version | head -1 >> compiler.txt
"
(cd "$out" && sha256sum libsnappy.so *.o > SHA256SUMS)
cat "$out/compiler.txt" "$out/SHA256SUMS"
