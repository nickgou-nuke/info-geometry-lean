#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd -- "$SCRIPT_DIR/../.." && pwd)"
MATHLIB_ROOT="$REPO_ROOT/.lake/packages/mathlib"
ROOT_TOOLCHAIN_FILE="$REPO_ROOT/lean-toolchain"
MATHLIB_TOOLCHAIN_FILE="$MATHLIB_ROOT/lean-toolchain"
MATHLIB_OLEAN="$MATHLIB_ROOT/.lake/build/lib/lean/Mathlib.olean"
STATE_DIR="$REPO_ROOT/.lake/cache-state"
LOCK_FILE="$STATE_DIR/mathlib-cache.lock"
MARKER_FILE="$STATE_DIR/mathlib-cache-hydrated"

if [[ ! -d "$MATHLIB_ROOT/.git" ]]; then
  echo "error: pinned local Mathlib checkout is missing: $MATHLIB_ROOT" >&2
  exit 1
fi

if [[ ! -f "$ROOT_TOOLCHAIN_FILE" || ! -f "$MATHLIB_TOOLCHAIN_FILE" ]]; then
  echo "error: root or Mathlib lean-toolchain file is missing" >&2
  exit 1
fi

ROOT_TOOLCHAIN="$(tr -d '[:space:]' < "$ROOT_TOOLCHAIN_FILE")"
MATHLIB_TOOLCHAIN="$(tr -d '[:space:]' < "$MATHLIB_TOOLCHAIN_FILE")"
if [[ "$ROOT_TOOLCHAIN" != "$MATHLIB_TOOLCHAIN" ]]; then
  echo "error: pinned toolchain mismatch" >&2
  echo "  root:    $ROOT_TOOLCHAIN" >&2
  echo "  mathlib: $MATHLIB_TOOLCHAIN" >&2
  exit 1
fi

MATHLIB_REV="$(git -C "$MATHLIB_ROOT" rev-parse HEAD)"
CACHE_ID="$ROOT_TOOLCHAIN $MATHLIB_REV"

mkdir -p "$STATE_DIR"
exec 9>"$LOCK_FILE"
if ! flock -n 9; then
  echo "error: Mathlib cache hydration is already running" >&2
  exit 1
fi

if [[ -f "$MATHLIB_OLEAN" ]]; then
  printf '%s\n' "$CACHE_ID" > "$MARKER_FILE"
  echo "[mathlib-cache] pinned artifacts already present"
  exit 0
fi

if [[ -f "$MARKER_FILE" ]] && [[ "$(<"$MARKER_FILE")" == "$CACHE_ID" ]]; then
  echo "error: cache hydration was already attempted for $CACHE_ID" >&2
  echo "error: refusing an automatic repeated download" >&2
  exit 1
fi

echo "[mathlib-cache] hydrating from pinned Mathlib workspace"
echo "[mathlib-cache] revision: $MATHLIB_REV"
echo "[mathlib-cache] toolchain: $ROOT_TOOLCHAIN"

(
  cd "$MATHLIB_ROOT"
  lake exe cache get
)

printf '%s\n' "$CACHE_ID" > "$MARKER_FILE"
echo "[mathlib-cache] hydration completed; repeat downloads are now blocked"
