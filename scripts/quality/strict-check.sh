#!/usr/bin/env bash
set -euo pipefail

echo "[strict-check] building canonical entrypoints with warnings as errors"
python3 tools/run_locked_lake_build.py InfoGeometry --wfail

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
ALLOWED_CANONICAL_RESEARCH_IMPORTS=()

mapfile -t canonical_research_import_lines < <(
  rg -n "^import InfoGeometry\\.Research\\.[A-Za-z0-9_.]+$" \
    "${CANONICAL_PATHS[@]}" -g '*.lean' || true
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

echo "[strict-check] enforcing quarantine boundary"
bash scripts/enforce_quarantine_imports.sh

echo "[strict-check] running constructivity audit on stable surface"
python3 scripts/quality/audit_constructivity.py --mode stable

echo "[strict-check] running surrogate dependency audit"
scripts/audit_surrogates.sh

echo "[strict-check] OK"
echo "[strict-check] running naming convention audit"
echo "[strict-check] running docstring audit"
echo "[strict-check] running style audit"
set +e
python3 scripts/quality/audit_naming.py
naming_status=$?
python3 scripts/quality/audit_docstrings.py
docstring_status=$?
python3 scripts/quality/audit_style.py
style_status=$?
set -e

if [[ $naming_status -ne 0 || $docstring_status -ne 0 || $style_status -ne 0 ]]; then
  echo "[strict-check] quality audits failed:"
  echo "  naming audit exit code: $naming_status"
  echo "  docstring audit exit code: $docstring_status"
  echo "  style audit exit code: $style_status"
  exit 1
fi

echo "[strict-check] running compiler bridge RPC regression tests"
python3 -m unittest tests.test_compiler_bridge_rpc

echo "[strict-check] all quality audits passed"
