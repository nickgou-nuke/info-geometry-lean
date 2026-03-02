#!/usr/bin/env bash
# audit_namespaces.sh
#
# Quick audit for Lean files that are missing a project namespace declaration.
# Default project namespace: InfoGeometry
#
# Usage:
#   bash scripts/audit_namespaces.sh
#   bash scripts/audit_namespaces.sh KLThesis
#   bash scripts/audit_namespaces.sh InfoGeometry ./InfoGeometry
#
# Notes:
# - This is a grep-based heuristic (fast, not a parser).
# - It ignores comments imperfectly, but works well in practice for audits.
# - It reports files that do NOT contain a line starting with `namespace <Project>`
#   anywhere in the file.

set -euo pipefail

PROJECT_NS="${1:-InfoGeometry}"
ROOT_DIR="${2:-./lean/InfoGeometry}"

if [[ ! -d "$ROOT_DIR" ]]; then
  echo "[audit] root directory not found: $ROOT_DIR" >&2
  exit 1
fi

echo "[audit] Project namespace: $PROJECT_NS"
echo "[audit] Scanning root:       $ROOT_DIR"
echo

# Collect Lean files (excluding build/tooling dirs if they live under root)
mapfile -t LEAN_FILES < <(
  find "$ROOT_DIR" -type f -name "*.lean" \
    ! -path "*/.lake/*" \
    ! -path "*/build/*" \
    | sort
)

if [[ ${#LEAN_FILES[@]} -eq 0 ]]; then
  echo "[audit] No .lean files found."
  exit 0
fi

missing=()
present=()

for f in "${LEAN_FILES[@]}"; do
  # Match lines like:
  #   namespace InfoGeometry
  #   namespace InfoGeometry.Foo
  #   namespace   InfoGeometry
  #
  # We intentionally do NOT count `open InfoGeometry` or `end InfoGeometry`.
  if grep -Eq "^[[:space:]]*namespace[[:space:]]+${PROJECT_NS}([.]|[[:space:]]|$)" "$f"; then
    present+=("$f")
  else
    missing+=("$f")
  fi
done

echo "[audit] Files with namespace ${PROJECT_NS}*: ${#present[@]}"
echo "[audit] Files missing namespace ${PROJECT_NS}*: ${#missing[@]}"
echo

if [[ ${#missing[@]} -gt 0 ]]; then
  echo "=== Missing namespace ${PROJECT_NS} ==="
  for f in "${missing[@]}"; do
    echo "$f"
  done
  echo
fi

# Optional: show files that declare *some* namespace, but not the project namespace
echo "=== Files declaring a non-${PROJECT_NS} namespace (heuristic) ==="
for f in "${missing[@]}"; do
  ns_line="$(grep -En "^[[:space:]]*namespace[[:space:]]+" "$f" | head -n 1 || true)"
  if [[ -n "$ns_line" ]]; then
    echo "$f :: $ns_line"
  fi
done
echo

# Optional: top namespace prefixes seen in the codebase
echo "=== Namespace prefix histogram (first namespace line per file) ==="
grep -RhoE "^[[:space:]]*namespace[[:space:]]+[A-Za-z0-9_.']+" "$ROOT_DIR" \
  | sed -E 's/^[[:space:]]*namespace[[:space:]]+//' \
  | sed -E 's/^([A-Za-z0-9_]+).*/\1/' \
  | sort | uniq -c | sort -nr | head -30 || true

echo
echo "[audit] Done."
