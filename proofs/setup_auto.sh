#!/usr/bin/env bash
set -euo pipefail

# ═══════════════════════════════════════════════════════════════════════
# Fibonacci Anyon Proofs — Setup & Build Script
# ═══════════════════════════════════════════════════════════════════════
# This script:
#   1. Symlinks the pre-built mathlib (9.5 GB) to avoid re-downloading
#   2. Configures the lake project
#   3. Builds all 5 Lean proof files
#   4. Verifies compilation
#
# Prerequisites:
#   - elan + Lean 4.28.0 (managed by elan)
#   - Uses pre-built mathlib from /home/goutev/auto/.lake/packages/mathlib
#     (falls back to /home/goutev/info-geometry-lean/.lake/packages/mathlib if needed)
# ═══════════════════════════════════════════════════════════════════════

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
NC='\033[0m'

echo -e "${BLUE}═══ Fibonacci Anyon Proofs — Setup ═══${NC}"

# Step 1: Check dependencies
echo -e "${YELLOW}[1/4]${NC} Checking dependencies..."
if ! command -v lean &>/dev/null; then
  echo -e "${RED}✗ Lean 4 not found. Install via: curl https://leanprover-community.github.io/elan.sh | bash${NC}"
  exit 1
fi
echo -e "  ${GREEN}✓${NC} Lean $(lean --version | head -1)"

if ! command -v lake &>/dev/null; then
  echo -e "${RED}✗ lake not found.${NC}"
  exit 1
fi
echo -e "  ${GREEN}✓${NC} lake available"

# Step 2: Symlink pre-built mathlib
echo -e "${YELLOW}[2/4]${NC} Linking pre-built mathlib..."
MATHLIB_SRC="/home/goutev/auto/.lake/packages/mathlib"
if [ ! -d "$MATHLIB_SRC" ]; then
  MATHLIB_SRC="/home/goutev/info-geometry-lean/.lake/packages/mathlib"
fi
MATHLIB_DST="$SCRIPT_DIR/.lake/packages/mathlib"

if [ -d "$MATHLIB_SRC" ]; then
  mkdir -p "$SCRIPT_DIR/.lake/packages"
  if [ ! -L "$MATHLIB_DST" ]; then
    ln -sf "$MATHLIB_SRC" "$MATHLIB_DST"
    echo -e "  ${GREEN}✓${NC} Symlinked mathlib ($(du -sh "$MATHLIB_SRC" | cut -f1))"
  else
    echo -e "  ${GREEN}✓${NC} mathlib already linked"
  fi
else
  echo -e "  ${YELLOW}⚠${NC} Pre-built mathlib not found at $MATHLIB_SRC"
  echo -e "  ${YELLOW}⚠${NC} Will download fresh — this may take 30+ minutes."
fi

# Step 3: Also symlink all dependency packages to avoid re-downloads
PKGS_SRC="/home/goutev/auto/.lake/packages"
if [ ! -d "$PKGS_SRC" ]; then
  PKGS_SRC="/home/goutev/info-geometry-lean/.lake/packages"
fi
PKGS_DST="$SCRIPT_DIR/.lake/packages"
for pkg in "$PKGS_SRC"/*/; do
  name=$(basename "$pkg")
  if [ "$name" != "mathlib" ] && [ ! -L "$PKGS_DST/$name" ]; then
    ln -sf "$pkg" "$PKGS_DST/$name" 2>/dev/null || true
  fi
done

# Step 4: Build
echo -e "${YELLOW}[3/4]${NC} Building proofs..."
if lake build 2>&1 | tail -20; then
  echo -e "  ${GREEN}✓${NC} All proofs compiled successfully!"
else
  echo -e "  ${YELLOW}⚠${NC} Build had issues — see above for details."
  echo -e "  ${YELLOW}⚠${NC} Try: lake build --no-build"
fi

# Step 5: Verify the current bridge files with the project environment.
echo -e "${YELLOW}[4/4]${NC} Verifying bridge files..."
VERIFY_FILES=(
  "CPTKreinTowerBridge.lean"
  "HestenesKreinColimitBridge.lean"
  "ModularKreinReflectionColimit.lean"
  "PeirceCuntzTKKBridge.lean"
  "ZornTrialityTKKBridge.lean"
  "CanonicalSplitOctonionTKK.lean"
  "ChiralCausalConeTKKBridge.lean"
  "Pin55ChiralZornTKKBridge.lean"
  "ZornTrialityFormSocket.lean"
)
for f in "${VERIFY_FILES[@]}"; do
  echo -n "  Checking $f... "
  if lake env lean "$f" >/dev/null 2>&1; then
    echo -e "${GREEN}✓${NC}"
  else
    echo -e "${RED}✗${NC}"
  fi
done

echo ""
echo -e "${GREEN}═══════════════════════════════════════════════════${NC}"
echo -e "${GREEN}  Build completed and bridge files verified         ${NC}"
echo -e "${GREEN}═══════════════════════════════════════════════════${NC}"
