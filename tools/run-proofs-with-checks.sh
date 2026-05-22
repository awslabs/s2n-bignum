#!/bin/bash
# Run proofs in a single arch/subdir, posting a GitHub Check Run per proof.
#
# Usage: run-proofs-with-checks.sh <arch> <subdir> <proof-deps-json> <changed-files-list>
#
# Reads the dep map; for each proof matching arch/subdir/, decides whether
# any changed file intersects its dep set; runs only those that intersect;
# posts queued/in_progress/conclusion check-runs to the PR's HEAD SHA.
#
# Exits 0 if all selected proofs pass (or none selected), nonzero otherwise.
#
# Required environment:
#   GITHUB_TOKEN, GITHUB_REPOSITORY, GITHUB_SHA -- set by Actions
#   HOLDIR                                      -- HOL Light location

set -euo pipefail

ARCH="$1"
SUBDIR="$2"
DEPS_JSON="$3"
CHANGED_LIST="$4"

if [ -z "${GITHUB_TOKEN:-}" ] || [ -z "${GITHUB_REPOSITORY:-}" ] || [ -z "${GITHUB_SHA:-}" ]; then
    echo "missing GITHUB_TOKEN/REPOSITORY/SHA" >&2
    exit 2
fi

post_check() {
    local proof="$1" status="$2" conclusion="${3:-}" detail="${4:-}"
    local payload
    if [ -n "$conclusion" ]; then
        payload=$(jq -n --arg name "proof: $proof" --arg sha "$GITHUB_SHA" --arg s "$status" --arg c "$conclusion" --arg d "$detail" \
          '{name: $name, head_sha: $sha, status: $s, conclusion: $c, output: {title: ("proof: " + $name), summary: $d}}')
    else
        payload=$(jq -n --arg name "proof: $proof" --arg sha "$GITHUB_SHA" --arg s "$status" \
          '{name: $name, head_sha: $sha, status: $s}')
    fi
    curl -fsS -X POST -H "Accept: application/vnd.github+json" \
        -H "Authorization: Bearer $GITHUB_TOKEN" \
        "https://api.github.com/repos/$GITHUB_REPOSITORY/check-runs" \
        -d "$payload" > /dev/null || true
}

# Find all proofs whose .S is in $ARCH/$SUBDIR/
mapfile -t all_proofs < <(jq -r --arg p "$ARCH/proofs/" 'keys[] | select(startswith($p))' "$DEPS_JSON")

# Restrict to those whose .S is in $ARCH/$SUBDIR/ (cross-check by stem)
selected=()
for proof in "${all_proofs[@]}"; do
    stem=$(basename "$proof" .ml)
    if [ -f "$ARCH/$SUBDIR/$stem.S" ]; then
        selected+=("$proof")
    fi
done

# Filter by changed files (any dep of the proof intersects the changed set)
to_run=()
if [ -s "$CHANGED_LIST" ]; then
    for proof in "${selected[@]}"; do
        # is any changed file in this proof's dep set?
        if jq -e --arg p "$proof" --slurpfile cf <(awk '{print "\"" $0 "\""}' "$CHANGED_LIST" | jq -s .) \
            '.[$p] as $deps | $cf[0] | any(. as $f | $deps | index($f))' "$DEPS_JSON" > /dev/null; then
            to_run+=("$proof")
        fi
    done
else
    to_run=("${selected[@]}")
fi

if [ ${#to_run[@]} -eq 0 ]; then
    echo "no changed files affect proofs in $ARCH/$SUBDIR; skipping"
    exit 0
fi

echo "${#to_run[@]} of ${#selected[@]} proofs in $ARCH/$SUBDIR will run"

# Build .native binaries for the selected proofs
natives=()
correctly=()
for proof in "${to_run[@]}"; do
    stem=$(basename "$proof" .ml)
    natives+=("$ARCH/$SUBDIR/$stem.native")
    correctly+=("$ARCH/$SUBDIR/$stem.correct")
done

(cd "$ARCH" && make -j ${BUILD_CORE_COUNT:-4} "${natives[@]#$ARCH/}")

# Run each proof, posting check-runs around it
fails=0
for i in "${!to_run[@]}"; do
    proof="${to_run[$i]}"
    target="${correctly[$i]}"
    stem=$(basename "$proof" .ml)
    post_check "$ARCH/$SUBDIR/$stem" in_progress
    if (cd "$ARCH" && make "${target#$ARCH/}"); then
        post_check "$ARCH/$SUBDIR/$stem" completed success "Proof passed."
    else
        post_check "$ARCH/$SUBDIR/$stem" completed failure "Proof failed; see job logs."
        fails=$((fails+1))
    fi
done

exit $fails
