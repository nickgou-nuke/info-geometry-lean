#!/usr/bin/env bash
# index_all_repos.sh
# Systematically converts all external_refs repos to v4.28.0, builds them,
# and indexes them with loogle.
set -euo pipefail

ROOT="/home/goutev/repos/info-geometry-lean"
REFS="$ROOT/external_refs"
LOOGLE="$REFS/loogle"
LOOGLE_BIN="$LOOGLE/.lake/build/bin/loogle"
LOOGLE_TC="$LOOGLE/lean-toolchain"
MATHLIB="$ROOT/.lake/packages/mathlib"
SUMMARY="$ROOT/scripts/infra/index_summary.json"

PASS=0
FAIL=0
SKIP=0

mkdir -p "$ROOT/scripts/infra"

echo '[]' > "$SUMMARY"

# Ensure loogle is built for v4.28.0
echo ">>> Ensuring loogle is built for v4.28.0..."
echo "leanprover/lean4:v4.28.0" > "$LOOGLE_TC"
cd "$LOOGLE"
lake build 2>&1 | tail -5

# All cached packages we can point to locally
declare -A CACHED_PKGS
for pkg in "$ROOT"/.lake/packages/*/; do
    name=$(basename "$pkg")
    CACHED_PKGS["$name"]="$pkg"
done

echo "Cached packages: ${!CACHED_PKGS[*]}"

# Files to NOT modify
SKIP_REPOS=("loogle" "." "..")

process_repo() {
    local repo="$1"
    local name
    name=$(basename "$repo")

    # Skip non-directories and excluded repos
    for skip in "${SKIP_REPOS[@]}"; do
        if [ "$name" = "$skip" ]; then
            echo ">>> Skipping $name"
            ((SKIP++))
            return
        fi
    done

    local tc="$repo/lean-toolchain"
    local lf="$repo/lakefile.lean"
    local manifest="$repo/lake-manifest.json"

    if [ ! -f "$lf" ]; then
        echo ">>> $name: no lakefile, skipping"
        ((SKIP++))
        return
    fi

    echo "=========================================="
    echo ">>> Processing $name..."
    echo "=========================================="

    # 1. Set toolchain to v4.28.0
    echo "leanprover/lean4:v4.28.0" > "$tc"

    # 2. Replace git dependencies with local paths in lakefile
    if grep -q "require mathlib from git" "$lf" 2>/dev/null; then
        echo ">>> $name: patching mathlib to local path..."
        sed -i 's|require mathlib from git.*$|require mathlib from "'"$MATHLIB"'"|' "$lf"
    fi

    # 3. Try to build
    echo ">>> $name: building..."
    cd "$repo"
    if lake build 2>&1 | tail -20; then
        echo ">>> $name: BUILD SUCCEEDED"
        ((PASS++))

        # 4. Index with loogle
        echo ">>> $name: indexing with loogle..."
        local mod_name="${name}-main"
        # Try to find the right module name
        local mods
        mods=$(grep -E '^lean_lib|^package' "$lf" 2>/dev/null | head -5 | sed 's/.*lean_lib //; s/ .*//; s/.*package //; s/ .*//' | tr -d '«"»' || echo "")
        if [ -n "$mods" ]; then
            for mod in $mods; do
                echo ">>> $name: loogle --module $mod '*'"
                lake env "$LOOGLE_BIN" --module "$mod" --index-mode use '*' 2>&1 || true
            done
        else
            lake env "$LOOGLE_BIN" '*' 2>&1 || true
        fi
    else
        echo ">>> $name: BUILD FAILED"
        ((FAIL++))
    fi

    echo ""
}

echo "=========================================="
echo "Starting batch build+index of all repos..."
echo "=========================================="

for d in "$REFS"/*/; do
    process_repo "$d"
done

echo "=========================================="
echo "Done!"
echo "Passed: $PASS, Failed: $FAIL, Skipped: $SKIP"
echo "=========================================="
