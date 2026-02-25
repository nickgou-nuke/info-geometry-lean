#!/usr/bin/env bash
set -euo pipefail

# List of canonical Lean source roots
CANONICAL_ROOTS=(lean/InfoGeometry)

# List of allowed non-source files in lean/
ALLOWED=(lakefile.lean lake-manifest.json lean-toolchain scripts all_lean_files_combined.lean InfoGeometry.lean)

# Find all files in lean/ that are not in canonical roots or allowed
find lean/ -maxdepth 1 -type f | while read -r file; do
  fname=$(basename "$file")
  skip=false
  for allowed in "${ALLOWED[@]}"; do
    if [[ "$fname" == "$allowed" ]]; then
      skip=true
      break
    fi
  done
  if ! $skip; then
    echo "[orphaned-check] Orphaned file in lean/: $fname"
    exit 1
  fi
done

# Find orphaned .lean files not in InfoGeometry, Archive, Experimental, or scripts
find lean/ -type f -name '*.lean' | while read -r file; do
  if [[ "$file" != lean/InfoGeometry/* ]] && [[ "$file" != lean/InfoGeometry/Archive/* ]] && [[ "$file" != lean/InfoGeometry/Experimental/* ]] && [[ "$file" != lean/scripts/* ]] && [[ "$file" != lean/InfoGeometry.lean ]]; then
    echo "[orphaned-check] Orphaned Lean file: $file"
    exit 1
  fi
done

# Optionally, check for empty folders
# Use a temporary file to avoid pipefail with grep if no empty dirs found
EMPTY_DIRS=$(find lean/ -type d -empty | grep -vE 'lean$|scripts$' || true)
if [[ -n "$EMPTY_DIRS" ]]; then
  echo "[orphaned-check] Empty directory found:"
  echo "$EMPTY_DIRS"
  exit 1
fi

echo "[orphaned-check] OK"
