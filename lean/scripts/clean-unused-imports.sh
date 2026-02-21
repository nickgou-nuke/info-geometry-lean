#!/usr/bin/env bash
set -euo pipefail

# Remove import statements flagged as unused in import-unused-list.txt
LIST=import-unused-list.txt
ROOT=$(pwd)

while IFS= read -r line; do
  file=${line%%:*}
  imp=${line#*:}
  # remove the exact import line using grep
  tmp=$(mktemp)
  grep -xFv "$imp" "$file" > "$tmp"
  mv "$tmp" "$file"
  echo "Removed from $file: $imp"
done < "$LIST"

echo "Cleanup complete. Run lake build to verify."