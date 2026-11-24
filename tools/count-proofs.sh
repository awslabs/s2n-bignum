#!/bin/bash
if [ "$#" -lt 1 ] || [ "$#" -gt 2 ]; then
  echo "count-proofs.sh <dir (e.g., arm)> [proof log directory]"
  exit 1
fi

arch_dir=$(cd "$1" && pwd) || exit 1
specs="$arch_dir/proofs/specifications.txt"
cd "${2:-$1}" || exit 1

num_correct_files=`find . -name "*.correct" | wc -l`
if [ $num_correct_files -eq 0 ]; then
  echo "No .correct file exists. Did you run 'make proofs'?"
  exit 1
fi

# An environment variable setting for consistent sorting results.
export LC_ALL=C

# Count the number of *_SUBROUTINE_CORRECT theorems that must be proven
num_correct_ans=`wc -l < "$specs"`
# Print & count the *_SUBROUTINE_CORRECT theorems that are actually proven
num_correct_out=`grep -e 'SUBROUTINE_CORRECT : thm' -e 'SUBROUTINE_SAFE : thm' */*.correct  | cut -f2 -d' ' | sort | uniq | wc -l`

# Print the *_SUBROUTINE_CORRECT theorems that are actually proven
proven_thms_log=`mktemp`
trap 'rm -f "$proven_thms_log"' EXIT
echo "Proven *_SUBROUTINE_{CORRECT,SAFE} theorems ($num_correct_out):"
grep -e 'SUBROUTINE_CORRECT : thm' -e 'SUBROUTINE_SAFE : thm' */*.correct  | cut -f2 -d' ' | sort | uniq > "$proven_thms_log"
cat "$proven_thms_log"

echo "Total # SUBROUTINE_CORRECT: ${num_correct_out}/${num_correct_ans}"
diff "$proven_thms_log" "$specs"
