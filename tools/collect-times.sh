#!/bin/bash
if [ "$#" -ne 1 ]; then
  echo "collect-times.sh <proof log dir>"
  echo "This script prints the timing line of every .correct log under the given"
  echo "directory: an architecture directory after 'make proofs', or"
  echo "<PROOF_OUTPUT>/<arch> after 'make fork-proofs'."
  exit 1
fi

s2n_bignum_arch=$1
cd "$s2n_bignum_arch" || exit 1

num_correct_files=`find . -name "*.correct" | wc -l`
if [ $num_correct_files -eq 0 ]; then
  echo "No .correct file exists. Did you run 'make proofs' or 'make fork-proofs'?"
  exit 1
fi
# grep must not detect anything including 'error' (case insensitive, '-i').
grep -r -i "Running time: " --include "*.correct"
