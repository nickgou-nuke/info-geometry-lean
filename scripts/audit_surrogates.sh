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

DECL_PATTERN="^[[:space:]]*(?:noncomputable[[:space:]]+)?(?:theorem|lemma|def|abbrev|structure|class|instance|axiom|inductive)[[:space:]]+($(printf '%s|' "${BANNED_SYMBOLS[@]}" | sed 's/|$//'))\\b"

echo "[surrogate-audit] checking for banned surrogate declarations in stable modules"
if rg -n "$DECL_PATTERN" "${IGNORE_GLOBS[@]}" "${SCAN_PATHS[@]}"; then
  echo "[surrogate-audit] banned surrogate declaration(s) detected in stable modules"
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

echo "[surrogate-audit] checking canonical surface for forbidden Canonical tactic usage"
CANONICAL_SURFACE_PATHS=(lean/InfoGeometry.lean lean/InfoGeometry/Library.lean lean/InfoGeometry/Canonical)
# Disallow keeping `canonical` tactic calls in stable modules; it is allowed only as a temporary synthesis helper.
# Match both:
#   - `by canonical`
#   - tactic-block line `canonical`
# Only match executable tactic syntax (not prose): canonical followed by `(`, `[`, number, or EOL.
CANONICAL_HITS=$(
  rg -n -g '*.lean' \
    "by[[:space:]]+canonical([[:space:]]*(\\[|\\(|[0-9]|$))|^[[:space:]]*canonical([[:space:]]*(\\[|\\(|[0-9]|$))" \
    "${CANONICAL_SURFACE_PATHS[@]}" \
  | rg -v ":[0-9]+:[[:space:]]*(--|/--|/-)" || true
)

if [[ -n "$CANONICAL_HITS" ]]; then
  echo "$CANONICAL_HITS"
  echo "[surrogate-audit] canonical tactic calls are forbidden in stable canonical modules"
  exit 1
fi

echo "[surrogate-audit] checking stable surface for exact nonconstructive patterns"
if ! python3 tools/quality/audit_constructivity.py --mode stable; then
  echo "[surrogate-audit] exact nonconstructive patterns detected in stable modules"
  exit 1
fi

echo "[surrogate-audit] checking stable surface for uninstantiated bridge assumptions and vacuous bridge debt"
python3 tools/generate_vacuity_index.py
if rg -n "vacuity gate: \\*\\*FAIL\\*\\*" VACUITY_INDEX.md >/dev/null; then
  echo "[surrogate-audit] vacuity debt detected on the stable surface"
  exit 1
fi

echo "[surrogate-audit] enforcing Pauli seal directives on canonical surface"
python3 tools/quality/pauli_seal_audit.py --root lean/InfoGeometry/Canonical --json-out reports/pauli-seal-audit.json

echo "[surrogate-audit] OK"
