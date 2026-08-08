#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/../.."

echo "=== Smoke Test: DumpLeanGraph Pipeline ==="

# 1. Syntax dump
echo "[1/3] DumpLeanGraph syntax extraction..."
lake env lean --run tools/lean_graph/DumpLeanGraph.lean \
  ChiralTLDescent.lean \
  B3PresentedGroup.lean \
  SupergradedCuntzBdG.lean \
  > /tmp/smoke_syntax.jsonl

# 2. Validate JSONL shape
echo "[2/3] Validate JSONL shape..."
python3 tools/lean_graph/check_dump_shape.py \
    --expect-keyword theorem \
    --expect-keyword structure \
    --expect-name ChiralTLDescent.chiral_left_tau_ideal \
    --expect-name B3PresentedGroup.phi \
    --expect-name SupergradedCuntzBdG.AffineWeylThermoEnsemble \
    --expect-name SupergradedCuntzBdG.ComplexStarCuntzBdGRepresentation \
  < /tmp/smoke_syntax.jsonl

# 3. Bridge with Environment layer
echo "[3/3] Bridge syntax + environment..."
lake env lean tools/lean_graph/ExtractGraph.lean
python3 tools/lean_graph/bridge_syntax_env.py \
  /tmp/smoke_syntax.jsonl proof_graph.json \
  > /tmp/smoke_bridged.json

echo ""
echo "=== Smoke test PASSED ==="
