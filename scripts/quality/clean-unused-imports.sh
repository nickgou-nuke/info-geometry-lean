#!/usr/bin/env bash
set -euo pipefail

# Remove import statements flagged as unused in import-unused-list.txt
# Supports optional dry-run mode and keeps backups of edited files.
# Usage: $0 [--dry-run]

# run from lean folder regardless of caller location
cd "$(dirname "$0")/.."  # project root
cd lean

LIST=import-unused-list.txt
DRY_RUN=false

while [[ $# -gt 0 ]]; do
  case $1 in
    --dry-run) DRY_RUN=true; shift ;;
    *) echo "unknown option: $1" >&2; exit 1 ;;
  esac
done

if [[ ! -r $LIST ]]; then
  echo "error: $LIST not found or not readable" >&2
  exit 1
fi

while IFS= read -r line; do
  file=${line%%:*}
  imp=${line#*:}

  if [[ ! -f $file ]]; then
    echo "warning: file $file does not exist, skipping" >&2
    continue
  fi

  if $DRY_RUN; then
    echo "[dry] would remove from $file: $imp"
    continue
  fi

  cp -a "$file" "$file.bak"
  tmp=$(mktemp)
  if grep -xFv "$imp" "$file" > "$tmp"; then
    mv "$tmp" "$file"
    echo "Removed from $file: $imp"
  else
    rm -f "$tmp"
    echo "error processing $file" >&2
  fi
done < "$LIST"

echo "Cleanup complete. Run lake build to verify."
