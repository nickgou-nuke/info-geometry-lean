#!/usr/bin/env bash
set -euo pipefail

ROOT=$(git rev-parse --show-toplevel)
cd "$ROOT"

if [ ! -d .lake/packages ]; then
  echo "No .lake/packages directory; skipping v4.28 policy check." >&2
  exit 0
fi

BAD=0
check_file() {
  local file="$1"
  while IFS= read -r line; do
    if [[ "$line" == *"leanprover/lean4:"* ]]; then
      if [[ "$line" != *"leanprover/lean4:v4.28.0"* ]]; then
        echo "$file: $line"
        BAD=1
      fi
    fi
    if [[ "$line" == *"rev = "* ]]; then
      if [[ "$line" =~ rev[[:space:]]*=[[:space:]]*"v4\.[0-9]+\.[0-9]+(-rc[0-9]+)?" ]]; then
        if [[ "$line" != *'rev = "v4.28.0"'* ]]; then
          echo "$file: $line"
          BAD=1
        fi
      fi
    fi
    if [[ "$line" == *'"inputRev": '* ]]; then
      if [[ "$line" =~ \"inputRev\"[[:space:]]*:[[:space:]]*"v4\.[0-9]+\.[0-9]+" ]]; then
        if [[ "$line" != *'"inputRev": "v4.28.0"'* ]]; then
          echo "$file: $line"
          BAD=1
        fi
      fi
    fi
  done < "$file"
}

# Only inspect package manifest / toolchain files.
mapfile -t FILES < <(find .lake/packages -type f \
  \( -name lean-toolchain -o -name lakefile.toml -o -name lakefile.lean -o -name lake-manifest.json \) | sort)

for f in "${FILES[@]}"; do
  check_file "$f"
done

if [[ $BAD -ne 0 ]]; then
  echo "Nested package policy violation: non-v4.28.0 pin detected in .lake/packages." >&2
  exit 1
fi

exit 0
