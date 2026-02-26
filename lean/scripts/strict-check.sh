#!/usr/bin/env bash
set -euo pipefail

echo "[strict-check] building InfoGeometry.Library with warnings as errors"
lake build InfoGeometry.Library --wfail

echo "[strict-check] elaborating InfoGeometry/Library.lean"
lake env lean lean/InfoGeometry/Library.lean

echo "[strict-check] elaborating canonical root InfoGeometry.lean"
lake env lean lean/InfoGeometry.lean

CANONICAL_PATHS=(lean/InfoGeometry.lean lean/InfoGeometry/Library.lean lean/InfoGeometry/Canonical)

echo "[strict-check] ensuring archive file is not imported by canonical modules"
if rg -n "all_lean_files_combined" "${CANONICAL_PATHS[@]}" -g '*.lean'; then
  echo "[strict-check] archive file must not be imported by canonical modules"
  exit 1
fi

echo "[strict-check] ensuring canonical modules do not import experimental umbrella"
if rg -n "^import InfoGeometry\\.Experimental$" \
  "${CANONICAL_PATHS[@]}" -g '*.lean'; then
  echo "[strict-check] canonical modules must not import InfoGeometry.Experimental"
  exit 1
fi

echo "[strict-check] enforcing canonical-to-research import allowlist"
ALLOWED_CANONICAL_RESEARCH_IMPORTS=(
  "InfoGeometry.Research.CartanDecomposition"
  "InfoGeometry.Research.Drazin"
  "InfoGeometry.Research.MoorePenrose"
  "InfoGeometry.Research.Triality"
)

mapfile -t canonical_research_import_lines < <(
  rg -n "^import InfoGeometry\\.Research\\.[A-Za-z0-9_.]+$" \
    "${CANONICAL_PATHS[@]}" -g '*.lean' -g '!ResearchPromoted.lean' || true
)

violations=()
for line in "${canonical_research_import_lines[@]}"; do
  mod=$(echo "$line" | sed -E 's/.*import (InfoGeometry\.Research\.[A-Za-z0-9_.]+).*/\1/')
  allowed=false
  for ok in "${ALLOWED_CANONICAL_RESEARCH_IMPORTS[@]}"; do
    if [[ "$mod" == "$ok" ]]; then
      allowed=true
      break
    fi
  done
  if [[ "$allowed" == false ]]; then
    violations+=("$line")
  fi
done

if [[ ${#violations[@]} -gt 0 ]]; then
  echo "[strict-check] disallowed canonical->research imports found:"
  printf '%s\n' "${violations[@]}"
  exit 1
fi

echo "[strict-check] checking for unresolved placeholders"
if rg -n "\\b(sorry|admit)\\b|content will be moved here" "${CANONICAL_PATHS[@]}" -g '*.lean'; then
  echo "[strict-check] placeholder content detected"
  exit 1
fi

echo "[strict-check] OK"
