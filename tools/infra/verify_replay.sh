#!/bin/bash
# Spire Replay Verifier (Rubedo Gate 3)
# Usage: ./verify_replay.sh <theorem_file> <manifest_json>

TARGET_FILE=$1
MANIFEST=$2

if [ -z "$TARGET_FILE" ] || [ -z "$MANIFEST" ]; then
    echo "Usage: ./verify_replay.sh <target_file> <manifest_json>"
    exit 1
fi

echo "--- [REPLAY] Verification Gate: $TARGET_FILE ---"

# 1. Integrity Check: Ensure no 'sorry' or 'axiom' in the target
if grep -q "sorry" "$TARGET_FILE"; then
    echo "REPLAY FAILURE: Found 'sorry' in the target file."
    exit 1
fi

if grep -q "axiom" "$TARGET_FILE"; then
    echo "REPLAY FAILURE: Found forbidden 'axiom' declaration."
    exit 1
fi

# 2. Build Check
echo "--- [REPLAY] Phase 1: Build Verification ---"
lake build
if [ $? -ne 0 ]; then
    echo "REPLAY FAILURE: Lake build failed."
    exit 1
fi

# 3. Semantic Stability Check
echo "--- [REPLAY] Phase 2: Semantic Audit ---"
python3 tools/infra/semantic_audit.py --task "$MANIFEST"
if [ $? -ne 0 ]; then
    echo "REPLAY FAILURE: Semantic audit drift detected."
    exit 1
fi

echo "--- [REPLAY] SUCCESS: Theorem has achieved Rubedo-closure. ---"
exit 0
