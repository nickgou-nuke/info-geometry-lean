#!/usr/bin/env bash
set -euo pipefail

# Canonical Lean source roots under lean/
ALLOWED_ROOT_DIRS=(InfoGeometry DAG Docs SelfReference Socratic scripts)
# Allowed top-level umbrella modules in lean/
ALLOWED_TOP_LEVEL_LEAN=(InfoGeometry.lean DAG.lean Docs.lean SelfReference.lean Socratic.lean)

is_allowed_top_level_lean() {
  local f="$1"
  for allowed in "${ALLOWED_TOP_LEVEL_LEAN[@]}"; do
    [[ "$f" == "$allowed" ]] && return 0
  done
  return 1
}

is_allowed_root_file() {
  local rel="$1"
  for d in "${ALLOWED_ROOT_DIRS[@]}"; do
    [[ "$rel" == "$d"/* ]] && return 0
  done
  return 1
}

# 1) top-level lean/ files must be known umbrella modules
while IFS= read -r file; do
  fname=$(basename "$file")
  if [[ "$fname" == *.lean ]] && ! is_allowed_top_level_lean "$fname"; then
    echo "[orphaned-check] Orphaned top-level Lean file in lean/: $fname"
    exit 1
  fi
done < <(find lean/ -maxdepth 1 -type f)

# 2) all .lean files must live in allowed roots or be allowed umbrella modules
while IFS= read -r file; do
  rel=${file#lean/}
  if is_allowed_top_level_lean "$rel"; then
    continue
  fi
  if ! is_allowed_root_file "$rel"; then
    echo "[orphaned-check] Orphaned Lean file: $file"
    exit 1
  fi
done < <(find lean/ -type f -name '*.lean')

# 3) optionally check for empty dirs (excluding lean root)
EMPTY_DIRS=$(find lean/ -type d -empty | grep -vE '^lean/$|^lean$' || true)
if [[ -n "$EMPTY_DIRS" ]]; then
  echo "[orphaned-check] Empty directory found:"
  echo "$EMPTY_DIRS"
  exit 1
fi

echo "[orphaned-check] OK"
