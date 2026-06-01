#!/bin/bash
# Spire Replay Verifier (Rubedo Gate 3)
# Usage: ./verify_replay.sh <theorem_file> <manifest_json>

set -euo pipefail

if [ "$#" -ne 2 ]; then
    echo "Usage: ./verify_replay.sh <target_file> <manifest_json>"
    exit 1
fi

TARGET_FILE="$1"
MANIFEST="$2"
REPO_ROOT="$(git rev-parse --show-toplevel)"

if [[ "$TARGET_FILE" = /* ]]; then
    if [[ "$TARGET_FILE" != "$REPO_ROOT/"* ]]; then
        echo "REPLAY FAILURE: target file must be inside repo root."
        exit 1
    fi
    TARGET_FILE="${TARGET_FILE#"$REPO_ROOT"/}"
fi

if [[ "$MANIFEST" = /* ]]; then
    if [[ "$MANIFEST" != "$REPO_ROOT/"* ]]; then
        echo "REPLAY FAILURE: manifest must be inside repo root."
        exit 1
    fi
    MANIFEST="${MANIFEST#"$REPO_ROOT"/}"
fi

TMPDIR="$(mktemp -d)"
REPLAY_REPO="$TMPDIR/replay_repo"
trap 'rm -rf "$TMPDIR"' EXIT

echo "--- [REPLAY] Fresh checkout gate for $TARGET_FILE ---"
git clone --quiet --depth 1 "file://$REPO_ROOT" "$REPLAY_REPO"
cd "$REPLAY_REPO"

# Seed Lake dependencies from local cache to keep replay offline-capable.
if [ -d "$REPO_ROOT/.lake/packages" ]; then
    mkdir -p .lake
    cp -a "$REPO_ROOT/.lake/packages" .lake/
fi

grep -q "\bsorry\b" "$TARGET_FILE" && {
    echo "REPLAY FAILURE: Found 'sorry' in $TARGET_FILE."
    exit 1
}

grep -q "\baxiom\b" "$TARGET_FILE" && {
    echo "REPLAY FAILURE: Found 'axiom' in $TARGET_FILE."
    exit 1
}

echo "--- [REPLAY] Phase 0: Hydrate precompiled mathlib cache ---"
lake exe cache get

echo "--- [REPLAY] Phase 1: Build verification ---"
lake build

echo "--- [REPLAY] Phase 2: Semantic audit ---"
python3 tools/infra/semantic_audit.py --task "$MANIFEST"

echo "--- [REPLAY] SUCCESS: isolated replay passed. ---"
