#!/usr/bin/env bash
set -euo pipefail

syntax_jsonl="$(mktemp)"
bridge_jsonl="$(mktemp)"
trap 'rm -f "$syntax_jsonl" "$bridge_jsonl"' EXIT

echo "=== Bridge Smoke Test ==="

# 1. Syntax dump
echo "[1/4] syntax dump..."
lake env lean --run tools/lean_graph/DumpLeanGraph.lean \
  SupergradedCuntzBdG.lean \
  ChiralTLDescent.lean \
  B3PresentedGroup.lean \
  > "$syntax_jsonl" 2>/tmp/smoke_stderr.txt

# 2. Environment dump
echo "[2/4] environment dump..."
lake env lean tools/lean_graph/ExtractGraph.lean 2>/dev/null

# 3. Join with syntax tree
echo "[3/4] join syntax+env..."
python3 tools/lean_graph/join_syntax_env.py \
  --syntax-jsonl "$syntax_jsonl" \
  --env-json proof_graph.json \
  --include-syntax-tree \
  --require-match B3PresentedGroup.phi \
  --require-match SupergradedCuntzBdG.AffineWeylThermoEnsemble \
  --require-match SupergradedCuntzBdG.ComplexStarCuntzBdGRepresentation \
  > "$bridge_jsonl"

# 4. Validate and dry-run import
echo "[4/4] validate bridge and dry-run import..."
python3 - "$bridge_jsonl" <<'PY'
import json, sys
path = sys.argv[1]
records = [json.loads(line) for line in open(path, encoding="utf-8") if line.strip()]
if not records:
    raise SystemExit("bridge_smoke_test: no records")
matched = sum(1 for r in records if r.get("matched"))
if not matched:
    raise SystemExit("bridge_smoke_test: no syntax matched environment")
print(f"bridge smoke: {len(records)} records, {matched} matched", file=sys.stderr)
PY

python3 tools/lean_graph/import_arango.py "$bridge_jsonl"

echo ""
echo "=== Bridge smoke test PASSED ==="
