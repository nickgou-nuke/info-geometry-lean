#!/usr/bin/env bash
# Build and index a single external_refs repo
# Usage: build_and_index.sh <repo-name>

set -euo pipefail

ROOT="/home/goutev/repos/info-geometry-lean"
REPO="$ROOT/external_refs/$1"
LOOGLE_BIN="$ROOT/external_refs/loogle/.lake/build/bin/loogle"

if [ ! -d "$REPO" ]; then
    echo "ERROR: repo $1 not found"
    exit 1
fi

echo "=========================================="
echo ">>> $1"
echo "=========================================="

cd "$REPO"

# 1. Set toolchain to v4.28.1
echo "leanprover/lean4:v4.28.1" > lean-toolchain

# 2. Change mathlib pin to v4.28.1 in lakefile (handle all formats)
if [ -f lakefile.lean ]; then
    # Format: require mathlib from git "URL" @ "v4.X.Y.Z"
    sed -i 's|@ "v4\.[0-9]*\.[0-9]*\(-rc[0-9]*\)\?"|@ "v4.28.1"|g' lakefile.lean
    # Format: require "mathlib" from git "URL" @ "commithash"
    sed -i 's|require "mathlib" from git "[^"]*" @ "[^"]*"|require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.1"|' lakefile.lean
fi

# 3. Update manifest to reflect v4.28.1 mathlib
if [ -f lake-manifest.json ]; then
    python3 -c "
import json
with open('lake-manifest.json') as f:
    data = json.load(f)
changed = False
for pkg in data.get('packages', []):
    if pkg.get('name') in ('mathlib', 'mathlib4'):
        pkg['rev'] = 'v4.28.1'
        changed = True
if changed:
    with open('lake-manifest.json', 'w') as f:
        json.dump(data, f, indent=2)
" 2>/dev/null || true
fi

# 4. Update deps and build
if lake update mathlib 2>&1; then
    if lake build 2>&1; then
        echo "  >>> BUILD OK ($1)"

        # 5. Find modules to index
        have_lib=false
        grep -E '^lean_lib' lakefile.lean 2>/dev/null | sed 's/.*lean_lib //; s/ .*//; s/«//g; s/»//g' | while read -r mod; do
            if [ -n "$mod" ]; then
                have_lib=true
                echo "  indexing $mod..."
                lake env "$LOOGLE_BIN" --module "$mod" --index-mode write 2>&1 | grep -v "^warning:" || true
            fi
        done

        # Also try the package name if no lean_lib found
        if ! $have_lib; then
            pkg_name=$(grep -E '^package' lakefile.lean 2>/dev/null | sed 's/.*package //; s/ .*//; s/«//g; s/»//g')
            if [ -n "$pkg_name" ]; then
                echo "  indexing $pkg_name..."
                lake env "$LOOGLE_BIN" --module "$pkg_name" --index-mode write 2>&1 | grep -v "^warning:" || true
            fi
        fi
    else
        echo "  >>> BUILD FAILED ($1) - build error"
        exit 1
    fi
else
    echo "  >>> BUILD FAILED ($1) - lake update failed"
    exit 1
fi
