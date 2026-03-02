#!/usr/bin/env bash
set -euo pipefail

# Script to audit imports in InfoGeometry sources.
# For each import, comment it out temporarily and test if the file still compiles.
# If compilation succeeds, the import is likely unnecessary.

# change to project root then lean subfolder
cd "$(dirname "$0")/.."  # project root
cd lean

BASE=InfoGeometry

echo "Starting import audit..."

audit_file() {
  local file="$1"
  # skip compatibility umbrellas (they are intentionally import-only)
  if grep -q "Compatibility umbrella" "$file"; then
    echo "\n== $file (skipped compatibility umbrella) =="
    return
  fi
  echo "\n== $file =="
  # read each import line
  grep '^import' "$file" | while read -r line; do
    # escape slashes for sed
    esc=$(printf '%s' "$line" | sed 's/[/]/\\&/g')
    # create a temp version with this import commented
    tmp=$(mktemp)
    sed "s/^${esc}/-- ${esc}/" "$file" > "$tmp"
    if lake env lean -q "$tmp" 2>/dev/null; then
      echo "UNUSED: $line"
    fi
    rm "$tmp"
  done
}

# iterate over all lean files under InfoGeometry
find "$BASE" -name '*.lean' | while read -r f; do
  audit_file "$f"
done

echo "Audit complete."