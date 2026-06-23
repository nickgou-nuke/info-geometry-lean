#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
cd "$ROOT"

OUT="artifacts/de_rham_klein_quadric/rank32_audit.json"
ARGS=()

while [[ $# -gt 0 ]]; do
  case "$1" in
    --out)
      OUT="$2"
      shift 2
      ;;
    --run|--dim|--signature)
      if [[ $# -lt 2 ]]; then
        echo "missing value for $1" >&2
        exit 2
      fi
      ARGS+=("$1" "$2")
      shift 2
      ;;
    *)
      ARGS+=("$1")
      shift
      ;;
  esac
done

python3 scripts/experiments/DeRhamKleinQuadric/audit_rank32.py --out "$OUT" "${ARGS[@]}"

echo "--- written: $OUT"
if [ -f "$OUT" ]; then
  tail -n 40 "$OUT"
fi
