#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

REPORT="reports/theory_audit.md"
mkdir -p reports

{
  echo "# Theory Audit Report"
  echo
  echo "Generated: $(date -u '+%Y-%m-%d %H:%M:%SZ')"
  echo
  echo "## Build toolchain status"
  if command -v lake >/dev/null 2>&1; then
    echo "- lake: available ($(command -v lake))"
    echo '```bash'
    lake --version || true
    echo '```'
  else
    echo "- lake: unavailable on PATH"
    if [ -x "$HOME/.elan/bin/lake" ]; then
      echo "- lake fallback: found at ~/.elan/bin/lake"
    else
      echo "- lake fallback: not found at ~/.elan/bin/lake"
    fi
  fi
  echo

  echo "## Placeholder proof debt (sorry/admit)"
  echo
  echo '```text'
  rg -n "\\b(sorry|admit)\\b" lean -g '*.lean' || true
  echo '```'
  echo
  SCOUNT=$(rg -n "\\b(sorry|admit)\\b" lean -g '*.lean' | wc -l || true)
  echo "- Total placeholder occurrences in tracked Lean tree: ${SCOUNT}"
  echo

  echo "## Axiom declarations"
  echo
  echo '```text'
  rg -n "^\\s*axiom\\b" lean -g '*.lean' || true
  echo '```'
  ACOUNT=$(rg -n "^\\s*axiom\\b" lean -g '*.lean' | wc -l || true)
  echo "- Total explicit axiom declarations: ${ACOUNT}"
  echo

  echo "## Namespace audit"
  echo
  echo '```text'
  bash scripts/quality/audit_namespaces.sh || true
  echo '```'
  echo

  echo "## Orphaned Lean file audit"
  echo
  echo '```text'
  bash scripts/quality/orphaned-check.sh || true
  echo '```'
  echo

  echo "## Quarantine Boundary Audit"
  echo
  echo '```text'
  bash scripts/enforce_quarantine_imports.sh || true
  echo '```'
  echo

  echo "## Exact Constructivity Audit"
  echo
  echo '```text'
  python3 scripts/docs/proof_gap_report.py --root lean --md-out /tmp/proof_gap_report.md --tex-out /tmp/proof_gap_report.tex || true
  echo '```'
  echo

echo "## Review-Only Surrogate Audit"
echo
echo '```text'
python3 scripts/docs/proof_gap_report.py --root lean --md-out /tmp/proof_gap_report.review.md --tex-out /tmp/proof_gap_report.review.tex || true
echo '```'
echo

echo "## Mathless Proposition Audit"
echo
echo '```text'
python3 scripts/quality/mathless_proof_audit.py --root lean --format text || true
echo '```'
echo

  echo "## Notes"
  echo "- This report is static when lake is unavailable; full proof checking requires successful lake build."
} > "$REPORT"

echo "[audit-theory] wrote $REPORT"
