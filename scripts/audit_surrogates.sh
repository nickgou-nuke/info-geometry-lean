#!/usr/bin/env bash
set -euo pipefail

# Hard gate: stable modules must not depend on surrogate symbols.
# Allowed location for surrogate placeholders: lean/InfoGeometry/Unstable/**

SCAN_PATHS=(lean)
IGNORE_GLOBS=(
  -g '!**/InfoGeometry/Unstable/**'
  -g '!**/InfoGeometry/Archive/**'
  -g '!**/tmp/**'
  -g '!**/tmp.lean'
)

echo "[surrogate-audit] checking for imports from InfoGeometry.Unstable in stable modules"
if rg -n "^import[[:space:]]+InfoGeometry\\.Unstable\\." "${IGNORE_GLOBS[@]}" "${SCAN_PATHS[@]}"; then
  echo "[surrogate-audit] stable modules must not import InfoGeometry.Unstable.*"
  exit 1
fi

echo "[surrogate-audit] checking for direct open/namespace references to InfoGeometry.Unstable"
if rg -n "^(open|namespace)[[:space:]]+InfoGeometry\\.Unstable(\\.|$)" \
  "${IGNORE_GLOBS[@]}" "${SCAN_PATHS[@]}"; then
  echo "[surrogate-audit] stable modules must not open/namespace InfoGeometry.Unstable.*"
  exit 1
fi

echo "[surrogate-audit] checking for placeholder/surrogate keywords outside allowed paths"
if rg -n -i "\\b(placeholder|surrogate)\\b" "${IGNORE_GLOBS[@]}" "${SCAN_PATHS[@]}"; then
  echo "[surrogate-audit] placeholder/surrogate markers are only allowed under InfoGeometry/Unstable or Archive"
  exit 1
fi

BANNED_SYMBOLS=(
  ibIteration
  ib_fixedPoint
  ib_iteration_descent
  ibInducedObservable
  seedKMSLaw_of_ibData
  kmsResidual_ibInducedObservable_eq_zero
  hResidualLeGap_of_ibInducedObservable
  sinkhorn_kmsControl_of_ibDynamics_concrete
  MongeAmpereRicciClosure
  ThermodynamicFromGeometricAlgebraic
  GeometricAlgebraicFromThermodynamic
  ChiralTorsionChentsovGibbsBridge
  QFTAxiomsLayer
  SUNGaugeInstantiation
  YangMillsMassGapBridge
  hBridge
)

PATTERN="\\b($(printf '%s|' "${BANNED_SYMBOLS[@]}" | sed 's/|$//'))\\b"

echo "[surrogate-audit] checking for banned surrogate symbols in stable modules"
if rg -n "$PATTERN" "${IGNORE_GLOBS[@]}" "${SCAN_PATHS[@]}"; then
  echo "[surrogate-audit] banned surrogate symbol(s) detected in stable modules"
  exit 1
fi

echo "[surrogate-audit] checking canonical modules for reflexive Prop wrappers (heuristic)"
REFLEXIVE_HITS=""
while IFS= read -r file; do
  hit=$(
    awk '
      function trim(s) { sub(/^[[:space:]]+/, "", s); sub(/[[:space:]]+$/, "", s); return s }
      function norm(s) { gsub(/[[:space:]]+/, "", s); return s }
      function check_body(body, lnum, dname) {
        body = trim(body)
        if (body == "") return
        split(body, parts, "--")
        body = trim(parts[1])
        if (body == "") return
        eq = index(body, "=")
        if (eq == 0) return
        lhs = substr(body, 1, eq - 1)
        rhs = substr(body, eq + 1)
        if (norm(lhs) == norm(rhs)) {
          printf "%s:%d: def %s has reflexive body `%s`\n", FILENAME, lnum, dname, body
        }
      }
      BEGIN { pending = 0; dline = 0; dname = "" }
      {
        if (pending == 1) {
          if ($0 ~ /^[[:space:]]*$/) next
          check_body($0, dline, dname)
          pending = 0
          next
        }

        if ($0 ~ /^[[:space:]]*def[[:space:]]+[A-Za-z0-9_'\''`]+.*:[[:space:]]*Prop[[:space:]]*:=/) {
          match($0, /^[[:space:]]*def[[:space:]]+([A-Za-z0-9_'\''`]+)/, m)
          dname = m[1]
          dline = NR
          split($0, chunks, ":=")
          body = ""
          if (length(chunks) > 1) body = chunks[2]
          if (trim(body) == "") {
            pending = 1
          } else {
            check_body(body, dline, dname)
          }
        }
      }
    ' "$file"
  )
  if [[ -n "$hit" ]]; then
    REFLEXIVE_HITS+="$hit"$'\n'
  fi
done < <(find lean/InfoGeometry/Canonical -type f -name '*.lean' | sort)

if [[ -n "$REFLEXIVE_HITS" ]]; then
  echo "$REFLEXIVE_HITS"
  echo "[surrogate-audit] reflexive Prop wrappers detected in canonical modules"
  exit 1
fi

echo "[surrogate-audit] OK"
